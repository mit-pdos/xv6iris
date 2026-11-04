/-
Weak/Prom: **G4 target (2) on track (a), MP WITH OWNERSHIP TRANSFER — definitions, setup** (stage S4a; plan rev 7 §4
"Gate G4" (2): "MP with ownership transfer (`sd x; fence rw,w; sd flag` / `ld flag; fence r,rw; ld x`), proving that
x's points-to moves").

Program (litmus front end, `x = 0x1000`, `flag = y = 0x2000`, image all zero):
H0 `sd x5,(x6); fence rw,w; sd x7,(x8)` (x5 = 42, x6 = x, x7 = 1, x8 = y) ‖ H1 `ld x5,(x6); fence r,rw; ld x7,(x8)`
(x6 = y, x8 = x).

The protocol (allocated at adequacy start, plan §3 "pre-allocated"; every message of `M` is classified by its
content, which is fixed because `M` is a parameter):
* x-messages (`isX`: exactly H0's `sd x` message) — their `pend` tokens form the BAG of x's points-to `xPts g M lw`
  ("the latest write to x is `lw`; every later x-message's `pend` is mine");
* flag messages (`isF`: exactly H0's `sd flag` message) — one DEPOSIT SLOT each, with content `fR g M t` = "x's
  points-to, with its latest write below `t`"; ONE claim token, held by H1;
* every other message is DEAD (its `pend` in a `deadInv`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALib
import Weak.Prom.CoreLitH

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The test, the message classes -/

/-- MP with ownership transfer (G4 (2)). -/
def mpOwnT : Test :=
  { harts := [[Weak.Prom.Ref.Lit.sd 5 6, Weak.Prom.Ref.Lit.fRWW, Weak.Prom.Ref.Lit.sd 7 8],
              [Weak.Prom.Ref.Lit.ld 5 6, Weak.Prom.Ref.Lit.fRRW, Weak.Prom.Ref.Lit.ld 7 8]]
    regs0 := [[(5, 42), (6, X), (7, 1), (8, Y)], [(6, Y), (8, X)]]
    img := []
    cond := Weak.Prom.Ref.Lit.mpFF.cond }

/-- H0's `sd x` message. -/
def xMsg : PMsg := ⟨(X : Int), toBytes 42 8, some 0, .plain⟩

/-- H0's `sd flag` message. -/
def fMsg : PMsg := ⟨(Y : Int), toBytes 1 8, some 0, .plain⟩

def isX (M : List PMsg) (t : Nat) : Bool := decide (msgAt M t = some xMsg)
def isF (M : List PMsg) (t : Nat) : Bool := decide (msgAt M t = some fMsg)
def isD (M : List PMsg) (t : Nat) : Bool := !isX M t && !isF M t

/-- The timestamps of `M`. -/
def rng (M : List PMsg) : List Nat := List.range' 1 M.length

/-- x's BAG above `lw`: the later x-messages. -/
def xBag (M : List PMsg) (lw : Nat) : List Nat := (rng M).filter (fun t => decide (lw < t) && isX M t)

theorem mem_rng {M : List PMsg} {t : Nat} : t ∈ rng M ↔ 1 ≤ t ∧ t ≤ M.length := by
  unfold rng; rw [List.mem_range'_1]; omega

theorem msgAt_le {M : List PMsg} {t : Nat} {m : PMsg} (h : msgAt M t = some m) : 1 ≤ t ∧ t ≤ M.length := by
  cases t with
  | zero => cases h
  | succ k => exact ⟨by omega, by have := (List.getElem?_eq_some_iff.1 h).1; omega⟩

/-- `xMsg` does not touch the flag; `fMsg` does not touch x. -/
theorem xMsg_byte_Y : xMsg.byteAt (Y : Int) = none := by decide

theorem fMsg_not_X (j : Nat) (hj : j < 8) : ¬ msgTouches fMsg ((X : Int) + j) := by
  rintro (h | ⟨k, len, hc, _⟩)
  · have : fMsg.byteAt ((X : Int) + j) = none := by
      unfold PMsg.byteAt; rw [if_neg (by simp [fMsg, X, Y]; omega)]
    rw [this] at h; cases h
  · cases hc

theorem xMsg_ne_fMsg : xMsg ≠ fMsg := by decide

theorem filter_filter_of {p q r : Nat → Bool} (h : ∀ t, (p t && q t) = r t) :
    ∀ (l : List Nat), (l.filter p).filter q = l.filter r
  | [] => rfl
  | a :: l => by
    have ih := filter_filter_of h l
    have ha := h a
    cases hp : p a <;> cases hq : q a <;> cases hr : r a <;>
      simp_all [List.filter_cons]

theorem split_F (M : List PMsg) :
    ((rng M).filter (fun t => !isX M t)).filter (isF M) = (rng M).filter (isF M) := by
  refine filter_filter_of (fun t => ?_) _
  cases hf : isF M t
  · simp
  · have : isX M t = false := by
      unfold isF at hf; unfold isX
      simp only [decide_eq_true_eq] at hf
      rw [hf]; simp [xMsg_ne_fMsg.symm]
    simp [this]

theorem split_D (M : List PMsg) :
    ((rng M).filter (fun t => !isX M t)).filter (fun t => !isF M t) = (rng M).filter (isD M) :=
  filter_filter_of (fun t => by simp [isD]) _

theorem split_X (M : List PMsg) : (rng M).filter (isX M) = xBag M 0 := by
  unfold xBag
  refine List.filter_congr (fun t ht => ?_)
  have := (mem_rng.1 ht).1
  simp [show 0 < t by omega]

/-! ## 2. Big-separating-conjunction plumbing over timestamp lists -/

section bigop

variable {GF : BundledGFunctors}

theorem bsl_range (F : Nat → IProp GF) : ∀ (l : List GName) (c : Nat),
    ([∗list] k ↦ _x ∈ l, F (k + c)) ⊢ [∗list] t ∈ List.range' c l.length, F t
  | [], _ => .rfl
  | _ :: l, c => by
    refine (BigSepL.bigSepL_cons).1.trans (Entails.trans ?_ (BigSepL.bigSepL_cons).2)
    refine sep_mono (by simp) ?_
    have := bsl_range F l (c + 1)
    simp only [show ∀ k, k + 1 + c = k + (c + 1) from fun k => by omega]
    exact this

theorem bsl_filter_split (F : Nat → IProp GF) (p : Nat → Bool) : ∀ (l : List Nat),
    ([∗list] t ∈ l, F t) ⊢ ([∗list] t ∈ l.filter p, F t) ∗ [∗list] t ∈ l.filter (fun t => !p t), F t
  | [] => by iintro _; isplitl <;> exact BigSepL.bigSepL_nil.2
  | a :: l => by
    have ih := bsl_filter_split F p l
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
    icases ih $$ H with ⟨H1, H2⟩
    cases hp : p a
    · rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos (by simp [hp])]
      iframe H1
      iapply (BigSepL.bigSepL_cons).2
      iframe Ha H2
    · rw [List.filter_cons_of_pos hp, List.filter_cons_of_neg (by simp [hp])]
      iframe H2
      iapply (BigSepL.bigSepL_cons).2
      iframe Ha H1

theorem bsl_filter_mono (F : Nat → IProp GF) (p q : Nat → Bool) (hpq : ∀ t, q t = true → p t = true) :
    ∀ (l : List Nat), ([∗list] t ∈ l.filter p, F t) ⊢ [∗list] t ∈ l.filter q, F t
  | [] => .rfl
  | a :: l => by
    have ih := bsl_filter_mono F p q hpq l
    cases hq : q a
    · rw [List.filter_cons_of_neg (p := q) (by simp [hq])]
      cases hp : p a
      · rw [List.filter_cons_of_neg (p := p) (by simp [hp])]; exact ih
      · rw [List.filter_cons_of_pos hp]
        iintro H
        icases (BigSepL.bigSepL_cons).1 $$ H with ⟨-, H⟩
        iapply ih $$ H
    · have hp := hpq a hq
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
      iapply (BigSepL.bigSepL_cons).2
      iframe Ha
      iapply ih $$ H

/-- Take one element out of a filtered list, keeping a smaller filter. -/
theorem bsl_filter_take (F : Nat → IProp GF) (p q : Nat → Bool) (ts : Nat) (hts : p ts = true)
    (hpq : ∀ t, q t = true → p t = true ∧ t ≠ ts) :
    ∀ (l : List Nat), ts ∈ l → l.Nodup → ([∗list] t ∈ l.filter p, F t) ⊢ F ts ∗ [∗list] t ∈ l.filter q, F t
  | [], h, _ => by cases h
  | a :: l, hm, hnd => by
    by_cases heq : a = ts
    · subst heq
      have hq : q a = false := by
        cases h : q a
        · rfl
        · exact absurd rfl (hpq a h).2
      rw [List.filter_cons_of_pos hts, List.filter_cons_of_neg (by simp [hq])]
      iintro H
      icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
      iframe Ha
      iapply bsl_filter_mono F p q (fun t ht => (hpq t ht).1) l $$ H
    · have hm' : ts ∈ l := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm heq
        · exact h
      have ih := bsl_filter_take F p q ts hts hpq l hm' (List.nodup_cons.1 hnd).2
      cases hp : p a
      · have hq : q a = false := by
          cases h : q a
          · rfl
          · rw [(hpq a h).1] at hp; cases hp
        rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_neg (by simp [hq])]; exact ih
      · rw [List.filter_cons_of_pos hp]
        iintro H
        icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
        icases ih $$ H with ⟨Hts, H⟩
        iframe Hts
        cases hq : q a
        · rw [List.filter_cons_of_neg (by simp [hq])]; iexact H
        · rw [List.filter_cons_of_pos hq]
          iapply (BigSepL.bigSepL_cons).2
          iframe Ha H

theorem bsl_mem {F : Nat → IProp GF} [∀ t, Persistent (F t)] {l : List Nat} {t : Nat} (h : t ∈ l) :
    ([∗list] u ∈ l, F u) ⊢ F t :=
  BigSepL.bigSepL_mem h

theorem bsl_fupd {hlc : HasLC} [InvGS_gen hlc GF] {F G : Nat → IProp GF} (hFG : ∀ t, F t ⊢ |={⊤}=> G t) :
    ∀ (l : List Nat), ([∗list] t ∈ l, F t) ⊢ |={⊤}=> [∗list] t ∈ l, G t
  | [] => by iintro _; imodintro; exact BigSepL.bigSepL_nil.2
  | a :: l => by
    have ih := bsl_fupd hFG l
    iintro H
    icases (BigSepL.bigSepL_cons).1 $$ H with ⟨Ha, H⟩
    imod hFG a $$ Ha with Ga
    imod ih $$ H with Gl
    imodintro
    iapply (BigSepL.bigSepL_cons).2
    iframe Ga Gl

end bigop

/-! ## 3. The resources -/

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- X'S POINTS-TO (plan §3 "Points-to, a hypothesis to validate", track (a) form): the latest write to x is `lw`
(H0's message, or the image when `lw = 0`), and the `pend` tokens of every later x-message are held here. -/
def xPts (g : AGN) (M : List PMsg) (lw : Nat) : IProp GF :=
  iprop(⌜1 ≤ lw → msgAt M lw = some xMsg⌝ ∗ [∗list] t ∈ xBag M lw, pend g t)

/-- The flag slots' content: x's points-to, its latest write below the flag message `t`. -/
def fR (g : AGN) (M : List PMsg) (t : Nat) : IProp GF := iprop(∃ lw, ⌜1 ≤ lw ∧ lw < t⌝ ∗ xPts g M lw)

/-- THE PROTOCOL'S PERSISTENT PART: the doom box, every flag slot, every dead message. -/
def mpCtx (g : AGN) (M : List PMsg) (γc : GName) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (isF M), slotInv g t (fR g M t) γc) ∗
    ([∗list] t ∈ (rng M).filter (isD M), deadInv g t))

instance (g : AGN) (M : List PMsg) (γc : GName) : Persistent (mpCtx (GF := GF) g M γc) := by
  unfold mpCtx; infer_instance

/-- THE SETUP (plan §3 "At adequacy start … for every index t in 1..|M|"): classify every message. -/
theorem mp_setup (g : AGN) (M : List PMsg) (hm : g.mn.length = M.length) :
    doomInv (GF := GF) g M ∗ ([∗list] k ↦ _x ∈ g.mn, pend g (k + 1)) ⊢
      |={⊤}=> ∃ γc, mpCtx g M γc ∗ xPts g M 0 ∗ token γc := by
  iintro ⟨#Hdoom, Hp⟩
  have h0 : ([∗list] k ↦ _x ∈ g.mn, pend (GF := GF) g (k + 1)) ⊢ [∗list] t ∈ rng M, pend g t := by
    have := bsl_range (pend (GF := GF) g) g.mn 1; rw [hm] at this; exact this
  ihave Hp := h0 $$ Hp
  have h1 := bsl_filter_split (pend (GF := GF) g) (isX M) (rng M)
  rw [split_X] at h1
  have h2 := bsl_filter_split (pend (GF := GF) g) (isF M) ((rng M).filter (fun t => !isX M t))
  rw [split_F, split_D] at h2
  ihave ⟨Hx, Hr⟩ := h1 $$ Hp
  ihave ⟨Hf, Hd⟩ := h2 $$ Hr
  imod token_alloc with ⟨%γc, Ht⟩
  imod bsl_fupd (G := fun t => slotInv g t (fR g M t) γc) (fun t => slot_alloc g t _ γc) _ $$ Hf with #Hs
  imod bsl_fupd (G := fun t => deadInv g t) (fun t => dead_alloc g t) _ $$ Hd with #Hdd
  imodintro
  iexists γc
  iframe Ht
  isplitl []
  · unfold mpCtx
    iframe Hdoom Hs Hdd
  · unfold xPts
    iframe Hx
    ipureintro; intro h; omega

end res

end Weak.Prom.OA
