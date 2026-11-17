/-
Weak/Mini: **L4 MiniCmp — the simulation invariant** (mini plan rev 4 §2 L4; Pulte et al. PLDI'19 AtoP.v
`sim_state`/`sim_view`/`sim_local`: "each view is the gmo position of the latest relevant event",
`view_of_eid`).

Fixed: a program `P` and a finite execution `C` (`miniCut P C`).  `vo e` = the number of stores of `C.g` up to `e`
(a store's timestamp).  `Inv P C h s H` relates hart `h`'s reference state `s` (a state of its cut path, `n` events
done) to the machine hart `H`:
* `H` is at `s`'s pc with `s`'s register VALUES;
* PAST form: every register view is below the timestamp of a load its taint names; `vrOld` (`vwOld`) below a past
  load's (store's);
* FUTURE form (each maintained through one ppo rule, rvwmo.adoc:278–302): `vrNew` below every future load's
  timestamp (rule 4), `vwNew` and `vcap` strictly below every future store's (rules 4, 11, 13), the coherence floor
  of a word strictly below every future store to it (rule 1), every store at or below the floor at or below the
  store each future load of the word reads (`coh2`: rules 1, 2 and the load value axiom);
* the forward bank holds, per word, the hart's po-latest store to it, with its timestamp and a forward view below
  every future load reading it (rule 12);
* the promise set is exactly the timestamps of the hart's future stores.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Mini.CmpVo
import Weak.Mini.CmpHart

namespace Weak.Mini.Cmp

open Weak.Mini Weak.Mini.Mach

section defs

variable (P : MProg) (C : MCut)

/-- The timestamp of `e` (Pulte `view_of_eid`). -/
def vo (e : EvId) : Nat := voL (C.evs P) C.g e

/-- The timestamp a load reads at: its store's, or 0 (the initial memory). -/
def kts : Option EvId → Nat
  | none => 0
  | some w => vo P C w

/-- The kind and address of hart `h`'s `j`-th event. -/
def kd (h j : Nat) : MK := ((C.evs P).ev (h, j)).kind
def pa (h j : Nat) : Nat := ((C.evs P).ev (h, j)).pa

/-- The number of events of hart `h` in the cut. -/
def NN (h : Nat) : Nat := (C.st P h).evs.length

/-- `v` is 0 or below the timestamp of an event `j` of hart `h` with `Q j`. -/
def dom (h : Nat) (Q : Nat → Prop) (v : Nat) : Prop := v = 0 ∨ ∃ j, Q j ∧ v ≤ vo P C (h, j)

/-- THE FORWARD BANK'S ENTRY for word `a` after `n` events (Pulte AtoP `FWDBANK`). -/
def fwdOk (h n a : Nat) : Option (Nat × Nat) → Prop
  | none => ∀ j, j < n → kd P C h j = .st → pa P C h j ≠ a
  | some (tf, vf) => ∃ j, j < n ∧ kd P C h j = .st ∧ pa P C h j = a ∧
      (∀ j2, j < j2 → j2 < n → kd P C h j2 = .st → pa P C h j2 ≠ a) ∧ tf = vo P C (h, j) ∧
      ∀ j', n ≤ j' → j' < NN P C h → kd P C h j' = .ld → pa P C h j' = a → (C.evs P).rf (h, j') (some (h, j)) →
        vf ≤ vo P C (h, j')

/-- THE SIMULATION INVARIANT (file header). -/
structure Inv (h : Nat) (s : Weak.Mini.MSt) (H : MHart) : Prop where
  pc : H.fr.pc = s.pc
  q : H.fr.q = []
  len : H.fr.regs.length = 32
  regs : ∀ r, H.fr.rd r = (s.rd r).1
  regLt : ∀ r, (s.rd r).1 < two64
  regv : ∀ r, 0 < r → r < 32 → dom P C h (· ∈ (s.rd r).2) (H.ws.regv r)
  vrOld : dom P C h (fun j => j < s.evs.length ∧ kd P C h j = .ld) H.ws.vrOld
  vwOld : dom P C h (fun j => j < s.evs.length ∧ kd P C h j = .st) H.ws.vwOld
  vrNew : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .ld → H.ws.vrNew ≤ vo P C (h, j)
  vwNew : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .st → H.ws.vwNew < vo P C (h, j)
  vcap : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .st → H.ws.vcap < vo P C (h, j)
  coh1 : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .st → H.ws.coh (pa P C h j) < vo P C (h, j)
  coh2 : ∀ j, s.evs.length ≤ j → j < NN P C h → kd P C h j = .ld → ∀ w ∈ C.g, ((C.evs P).ev w).kind = .st →
    ((C.evs P).ev w).pa = pa P C h j → vo P C w ≤ H.ws.coh (pa P C h j) → ∀ o, (C.evs P).rf (h, j) o →
      vo P C w ≤ kts P C o
  fwd : ∀ a, fwdOk P C h s.evs.length a (H.ws.fwd a)
  ldv : H.ws.ldv = 0
  prom : ∀ t, t ∈ H.prom ↔ ∃ j, s.evs.length ≤ j ∧ j < NN P C h ∧ kd P C h j = .st ∧ vo P C (h, j) = t

end defs

/-! ## 1. The cut's events -/

section facts

variable {P : MProg} {C : MCut}

theorem ev_eq {h j : Nat} (hj : j < NN P C h) : (C.evs P).ev (h, j) = (C.st P h).evs[j] := by
  show (((C.st P h).evs[j]?).getD default) = _
  rw [List.getElem?_eq_getElem hj]; rfl

theorem ev_of {h j : Nat} {e : MEv} (hj : (C.st P h).evs[j]? = some e) : (C.evs P).ev (h, j) = e := by
  show (((C.st P h).evs[j]?).getD default) = _
  rw [hj]; rfl

theorem st_prefix (h : Nat) {k : Nat} (hk : k ≤ C.ks h) : (mrun P C.V h k).evs <+: (C.st P h).evs :=
  mrun_mono P C.V h hk

theorem ev_run {h j k : Nat} {e : MEv} (hk : k ≤ C.ks h) (hj : (mrun P C.V h k).evs[j]? = some e) :
    (C.evs P).ev (h, j) = e ∧ j < NN P C h := by
  obtain ⟨t, ht⟩ := st_prefix (C := C) h hk
  have hl := (List.getElem?_eq_some_iff.1 hj).1
  have h2 : (C.st P h).evs[j]? = some e := by
    rw [← ht, List.getElem?_append_left hl]; exact hj
  exact ⟨ev_of h2, (List.getElem?_eq_some_iff.1 h2).1⟩

theorem po_hj {h j1 j2 : Nat} (h12 : j1 < j2) (hj2 : j2 < NN P C h) : (C.evs P).po (h, j1) (h, j2) := by
  refine ⟨rfl, ?_⟩
  rw [ev_eq (by omega), ev_eq hj2]
  have hl : j2 < (mrun P C.V h (C.ks h)).evs.length := hj2
  exact List.pairwise_iff_getElem.1 (mrun_wf P C.V h (C.ks h)).ii_mono j1 j2 (by omega) hl h12

theorem isMem_hj {h j : Nat} (hh : h < P.harts.length) (hj : j < NN P C h)
    (hk : kd P C h j = .ld ∨ kd P C h j = .st) : (C.evs P).isMem (h, j) := ⟨⟨hh, hj⟩, hk⟩

/-- A load named by a taint of a cut state is a load of the cut. -/
theorem ldAt_cut {h k j : Nat} (hk : k ≤ C.ks h) (hl : ldAt (mrun P C.V h k).evs j) :
    j < (mrun P C.V h k).evs.length ∧ kd P C h j = .ld ∧ j < NN P C h := by
  obtain ⟨e, he, hkd⟩ := hl
  obtain ⟨h1, h2⟩ := ev_run hk he
  exact ⟨(List.getElem?_eq_some_iff.1 he).1, by unfold kd; rw [h1]; exact hkd, h2⟩

variable (hC : miniCut P C)
include hC

theorem mem_g (e : EvId) : e ∈ C.g ↔ (C.evs P).isMem e := hC.2.1 e
theorem hgmo : (C.evs P).gmoOk := hC.2.2.2.1
theorem hlva : (C.evs P).loadValueAx P.ini := hC.2.2.2.2.2.1

theorem ppoG {a b : EvId} (ha : (C.evs P).isMem a) (hb : (C.evs P).isMem b) (hpo : (C.evs P).po a b)
    (hr : (C.evs P).rule1 a b ∨ (C.evs P).rule2 a b ∨ (C.evs P).rule4 a b ∨ (C.evs P).rule9 a b ∨
      (C.evs P).rule10 a b ∨ (C.evs P).rule11 a b ∨ (C.evs P).rule12 a b ∨ (C.evs P).rule13 a b) :
    (C.evs P).gmo a b := hC.2.2.2.2.1 a b ⟨ha, hb, hpo, hr⟩

/-! ## 2. Timestamps -/

theorem vo_gmo {a b : EvId} (h : (C.evs P).gmo a b) : vo P C a + stc (C.evs P) b ≤ vo P C b :=
  voL_lt C.g h.1 h.2.1 h.2.2

theorem vo_gmo_le {a b : EvId} (h : (C.evs P).gmo a b) : vo P C a ≤ vo P C b := by
  have := vo_gmo hC h; omega

theorem vo_gmo_st {a b : EvId} (h : (C.evs P).gmo a b) (hb : ((C.evs P).ev b).kind = .st) :
    vo P C a < vo P C b := by
  have := vo_gmo hC h; rw [stc_st hb] at this; omega

theorem vo_pos {w : EvId} (hw : w ∈ C.g) (hs : ((C.evs P).ev w).kind = .st) : 1 ≤ vo P C w := by
  have := stc_le (A := C.evs P) C.g hw; rw [stc_st hs] at this; exact this

/-- A store at or below a memory operation's timestamp is gmo-before it. -/
theorem gmo_of_vo {w r : EvId} (hw : (C.evs P).isMem w) (hs : ((C.evs P).ev w).kind = .st)
    (hr : (C.evs P).isMem r) (hne : w ≠ r) (hle : vo P C w ≤ vo P C r) : (C.evs P).gmo w r := by
  rcases MEvsF.gmo_total (hgmo hC) hw hr hne with h | h
  · exact h
  · have := vo_gmo_st hC h hs; omega

/-- Two stores: at or below in timestamp = equal or gmo-before. -/
theorem st_of_vo {w w' : EvId} (hw : (C.evs P).isMem w) (hw' : (C.evs P).isMem w')
    (hs' : ((C.evs P).ev w').kind = .st) (hle : vo P C w' ≤ vo P C w) : w' = w ∨ (C.evs P).gmo w' w := by
  by_cases he : w' = w
  · exact .inl he
  · exact .inr (gmo_of_vo hC hw' hs' hw he hle)

theorem kts_ge {r w : EvId} {o : Option EvId} (hrf : (C.evs P).rf r o) (hc : (C.evs P).cand r w) :
    vo P C w ≤ kts P C o := by
  match o, hrf with
  | none, hrf => exact absurd hc (hrf w)
  | some w0, hrf =>
    rcases hrf.2 w hc with h | h
    · rw [h]; exact Nat.le_refl _
    · exact vo_gmo_le hC h

end facts

/-! ## 3. Views of sources -/

section views

variable {P : MProg} {C : MCut}

theorem dom_le {h : Nat} {Q : Nat → Prop} {v X : Nat} (hd : dom P C h Q v) (hX : ∀ j, Q j → vo P C (h, j) ≤ X) :
    v ≤ X := by
  rcases hd with h0 | ⟨j, hj, hv⟩
  · omega
  · have := hX j hj; omega

theorem dom_lt {h : Nat} {Q : Nat → Prop} {v X : Nat} (hd : dom P C h Q v) (hX : ∀ j, Q j → vo P C (h, j) < X)
    (hpos : 0 < X) : v < X := by
  rcases hd with h0 | ⟨j, hj, hv⟩
  · omega
  · have := hX j hj; omega

theorem dom_mono {h : Nat} {Q Q' : Nat → Prop} {v : Nat} (hd : dom P C h Q v) (hQ : ∀ j, Q j → Q' j) :
    dom P C h Q' v := by
  rcases hd with h0 | ⟨j, hj, hv⟩
  · exact .inl h0
  · exact .inr ⟨j, hQ j hj, hv⟩

theorem dom_max {h : Nat} {Q : Nat → Prop} {a b : Nat} (ha : dom P C h Q a) (hb : dom P C h Q b) :
    dom P C h Q (max a b) := by
  rcases Nat.le_total a b with hab | hab
  · rw [Nat.max_eq_right hab]; exact hb
  · rw [Nat.max_eq_left hab]; exact ha

theorem srcsView_append (ws : Mach.MSt) (a b : List MSrc) :
    srcsView ws (a ++ b) = max (srcsView ws a) (srcsView ws b) := by
  induction a with
  | nil => simp [srcsView]
  | cons x t ih =>
    simp only [List.cons_append, srcsView, List.foldr_cons] at ih ⊢
    rw [ih]; omega

theorem srcsView_srcR (ws : Mach.MSt) (r : Nat) : srcsView ws (srcR r) = if r = 0 then 0 else ws.regv r := by
  unfold srcR; split
  · rfl
  · simp [srcsView, srcView]

theorem srcsView_ld (ws : Mach.MSt) : srcsView ws [.ldres] = ws.ldv := by simp [srcsView, srcView]

theorem dom_srcR {h : Nat} {s : Weak.Mini.MSt} {ws : Mach.MSt}
    (hregv : ∀ r, 0 < r → r < 32 → dom P C h (· ∈ (s.rd r).2) (ws.regv r)) {r : Nat} (hr : r < 32) :
    dom P C h (· ∈ (s.rd r).2) (srcsView ws (srcR r)) := by
  rw [srcsView_srcR]; split
  · exact .inl rfl
  · exact hregv r (by omega) hr

/-- The effect of `regWL rd srcs ++ [instr]`. -/
theorem foldl_regWL (ws : Mach.MSt) (rd : Nat) (srcs : List MSrc) :
    (regWL rd srcs ++ [MLab.instr]).foldl eff ws =
      { ws with regv := fun r => if rd ≠ 0 ∧ r = rd then srcsView ws srcs else ws.regv r, ldv := 0 } := by
  unfold regWL
  by_cases h : rd = 0
  · simp only [h, if_true, List.nil_append, List.foldl_cons, List.foldl_nil, eff]
    first | rfl | (congr; funext r; simp)
  · simp only [h, if_false, List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil, eff]
    first | rfl | (congr; funext r; simp [h])

theorem regWL_af (rd : Nat) (srcs : List MSrc) : ∀ l ∈ regWL rd srcs ++ [MLab.instr], AF l := by
  intro l hl; unfold regWL at hl
  split at hl <;> simp at hl <;> rcases hl with rfl | rfl <;> trivial

theorem regWL_cons (rd : Nat) (srcs : List MSrc) :
    ∃ l0 rest, regWL rd srcs ++ [MLab.instr] = l0 :: rest := by
  unfold regWL; split
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- Register read after a write, on the machine side (MachCert `LP.wr_rd`). -/
theorem front_rd_wr (f : MFront) (pc : Nat) (q : List MLab) (rd v r : Nat) :
    (⟨pc, f.wr rd v, q⟩ : MFront).rd r =
      if rd ≠ 0 ∧ r = rd ∧ rd < f.regs.length then v % two64 else f.rd r := by
  unfold MFront.wr MFront.rd
  by_cases h0 : rd = 0
  · simp [h0]
  · simp only [h0, if_false]
    by_cases hr0 : r = 0
    · simp only [hr0, if_true]
      split
      · rename_i hh; exact absurd hh.2.1.symm h0
      · rfl
    · simp only [hr0, if_false]
      by_cases hrr : r = rd
      · subst hrr
        by_cases hl : r < f.regs.length
        · simp [hl, hr0]
        · simp [hl, hr0]
      · simp [hrr, List.getElem?_set_ne (Ne.symm hrr)]

theorem front_rd_same (f : MFront) (pc : Nat) (q : List MLab) (r : Nat) :
    (⟨pc, f.regs, q⟩ : MFront).rd r = f.rd r := rfl

theorem front_wr_len (f : MFront) (rd v : Nat) : (f.wr rd v).length = f.regs.length := by
  unfold MFront.wr; split <;> simp

/-- The register file after a write, on both sides. -/
theorem regs_wr2 {f : MFront} {s : Weak.Mini.MSt} (hl : f.regs.length = 32) (heq : ∀ r, f.rd r = (s.rd r).1)
    (pc : Nat) (q : List MLab) (rd v : Nat) (x : Nat × List Nat) (hv : v % two64 = x.1) :
    ∀ r, (⟨pc, f.wr rd v, q⟩ : MFront).rd r = ((s.wr rd x).rd r).1 := by
  intro r
  rw [front_rd_wr, Cmp.rd_wr, hl]
  by_cases h : 0 < rd ∧ rd < 32 ∧ r = rd
  · rw [if_pos ⟨by omega, h.2.2, h.2.1⟩, if_pos h]; exact hv
  · rw [if_neg h, if_neg (fun h' => h ⟨by omega, h'.2.2, h'.2.1⟩)]; exact heq r

theorem regLt_wr {s : Weak.Mini.MSt} (hlt : ∀ r, (s.rd r).1 < two64) (rd : Nat) (x : Nat × List Nat)
    (hx : x.1 < two64) : ∀ r, ((s.wr rd x).rd r).1 < two64 := by
  intro r; rw [Cmp.rd_wr]; split
  · exact hx
  · exact hlt r

theorem aluOp_lt (op : MAlu) {a b : Nat} (ha : a < two64) (hb : b < two64) : op.eval a b < two64 := by
  have h64 : two64 = 2 ^ 64 := rfl
  cases op with
  | add => exact Nat.mod_lt _ (by decide)
  | sub => exact Nat.mod_lt _ (by decide)
  | xor => simp only [MAlu.eval]; rw [h64] at *; exact Nat.xor_lt_two_pow ha hb
  | or => simp only [MAlu.eval]; rw [h64] at *; exact Nat.or_lt_two_pow ha hb
  | and => simp only [MAlu.eval]; rw [h64] at *; exact Nat.and_lt_two_pow _ hb
  | sll => exact Nat.mod_lt _ (by decide)
  | srl => simp only [MAlu.eval]; exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
  | sra =>
    simp only [MAlu.eval]
    split
    · exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha
    · rw [h64] at *
      apply Nat.or_lt_two_pow (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) ha)
      have : 0 < 2 ^ (64 - b % 64) := Nat.two_pow_pos _
      have h2 : (2 : Nat) ^ 64 = two64 := rfl
      omega
  | slt => simp only [MAlu.eval]; split <;> decide
  | sltu => simp only [MAlu.eval]; split <;> decide
  | mul => exact Nat.mod_lt _ (by decide)

end views

end Weak.Mini.Cmp
