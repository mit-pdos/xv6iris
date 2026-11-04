/-
Weak/Prom: **completeness (reference ⊆ machine v2), stage S3a — definitions** (plan of record rev 7
`~/dev/weak-orch/promising/plan.md` §0 "(T-cmp)", §6 "Strategy, following Pulte AtoP.v", §8 "S3a").

What `rvwmo_complete` (Weak/Prom/CmpRun.lean) is about, and the vocabulary it is stated in:

* THE SCOPE (S3a, phase 1 [OWN.P3]).
  - `progS3aB T` — a SYNTACTIC check of the litmus program: no I/O regions; every instruction is one of the S3a
    subset (ALU, plain loads and stores of 1, 2, 4 or 8 bytes, FENCE, FENCE.TSO, branches, jumps, `csrr`,
    `fence.i`, `nop`; registers `< 32`; ALU immediates `< 2^64`, Ref.lean's "64-bit two's-complement naturals");
    initial memory bytes `< 256`.  NOT in S3a (plan §6 table): AMOs, LR/SC (S3b), Zalasr / RCpc annotations
    (rules 5–8 are S3b's), mixed-size (S3c), translation (deferred, [OWN.P3]).
  - `singleSize X` — NA-6 verbatim (plan §9: "every byte is always accessed at one width and alignment"), on the
    execution: two memory operations that access a common byte have the same address and the same size.
    Mixed-size completeness is S3c, deferred by [OWN.P5].
  - `platformOrd X` — plan §0's platform hypothesis.  With translation off and the litmus front end, the
    reference has no implicit-read events (no walks, no A/D pairs; fetches are not modelled by the litmus ISA),
    so PA-0/PA-1/PA-3/PA-5 have nothing to constrain: `platformOrd` is `True`.  Kept as a named hypothesis so the
    theorem has the plan's shape; the translation extension replaces it.
* THE MEMORY OF A REFERENCE EXECUTION (plan §6: "`mem_of_ex` takes the writes in ob order (AtoP.v:26–35). Our gmo
  is given, so M := writes in gmo order"): `memG X g` = the stores of `g`, in order, as machine messages
  (`msgOf`: address, written bytes, author, class `plain`); `memOf X = memG X X.gmo`.
* THE VIEW OF AN EVENT (Pulte's `view_of_eid`, AtoP.v:61): `voG X g e` = the number of stores of `g` up to `e`,
  `e` included when it is a store.  So a store's view is its timestamp in `memOf X`, and a load's view is the
  number of stores before it in gmo.
* OBSERVATIONS (plan §0: "`rowObs` is a hart's label stream with every answered byte"; litmus level: the loads'
  answered bytes, in program order): `refRow X h` (reference) and `machRow τ` (machine trace).
* `domF` — Pulte's `sim_view` (AtoP.v:150–156): a view is `0` or below the view of some event in a set.

No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.RefCheck
import Weak.Prom.MachCert
import Weak.Prom.CoreDefs

namespace Weak.Prom.Cmp

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref

/-! ## 1. Scope -/

/-- An access size of the litmus ISA's plain loads and stores (`lb/lh/lw/ld`, `sb/sh/sw/sd`). -/
def szOk (sz : Nat) : Bool := sz == 1 || sz == 2 || sz == 4 || sz == 8

/-- A register operand of RV64I. -/
def rOk (r : Nat) : Bool := decide (r < 32)

/-- THE S3a INSTRUCTION SUBSET (plan §6 table, row S3a: "single-size plain loads and stores, all fences incl.
FENCE.TSO, deps …, forwarding, rules 1–4 and 9–13"), with operand well-formedness. -/
def instrS3a : Instr → Bool
  | .alui _ rd rs1 imm => rOk rd && rOk rs1 && decide (imm < two64)
  | .alu _ rd rs1 rs2 => rOk rd && rOk rs1 && rOk rs2
  | .load sz _ rd rs1 _ => szOk sz && rOk rd && rOk rs1
  | .store sz rs2 rs1 _ => szOk sz && rOk rs2 && rOk rs1
  | .fence _ => true
  | .fenceTso => true
  | .br _ rs1 rs2 _ => rOk rs1 && rOk rs2
  | .jmp _ => true
  | .csrr rd _ => rOk rd
  | .fencei => true
  | .nop => true
  | _ => false

/-- THE S3a PROGRAM SCOPE, a Bool (checked by `decide` per test). -/
def progS3aB (T : Test) : Bool :=
  T.io.isEmpty && T.harts.all (fun p => p.all instrS3a) && T.img.all (fun xv => decide (xv.2 < 256))

/-- NA-6, single-size (plan §9 NA-6, §Q2 (B): "executions where every byte is always accessed at one width and
alignment"): two memory operations that access a common byte have the same address and the same size. -/
def singleSize (X : Exec) : Prop :=
  ∀ a ∈ X.ids, ∀ b ∈ X.ids, (X.sk a).kind.isMem = true → (X.sk b).kind.isMem = true →
    overlapB (X.ev a) (X.ev b) = true → (X.ev a).pa = (X.ev b).pa ∧ (X.sk a).sz = (X.sk b).sz

/-- Plan §0's `platformOrd G`: the quoted platform facts about implicit reads (PA-0, PA-1, PA-3, PA-5).  The
litmus reference has no implicit-read events (translation off, [OWN.P3]; no fetch events), so it is `True`. -/
def platformOrd (_ : Exec) : Prop := True

/-! ## 2. The memory of an execution, the view of an event -/

/-- `e` is a store operation. -/
def isSt (X : Exec) (e : EvId) : Bool := (X.sk e).kind.isStore

/-- The machine message of store `e` (Pulte `mem_of_ex`'s `Msg.mk loc val tid`). -/
def msgOf (X : Exec) (e : EvId) : PMsg := ⟨((X.ev e).pa : Int), (X.ev e).wdat.map bv8, some e.1, .plain⟩

/-- `1` for a store, `0` otherwise. -/
def stCnt (X : Exec) (e : EvId) : Nat := if isSt X e then 1 else 0

/-- THE VIEW OF EVENT `e` in the order `g` (Pulte `view_of_eid`): the number of stores of `g` up to `e`. -/
def voG (X : Exec) : List EvId → EvId → Nat
  | [], _ => 0
  | x :: t, e => if x = e then stCnt X x else stCnt X x + voG X t e

/-- THE MEMORY of the order `g`: its stores, in order, as messages (plan §6 "M := writes in gmo order"). -/
def memG (X : Exec) (g : List EvId) : List PMsg := (g.filter (isSt X)).map (msgOf X)

/-- The final memory of execution `X` (`memOf G` of plan §0). -/
def memOf (X : Exec) : List PMsg := memG X X.gmo

/-- The view of event `e` in `X`'s global memory order. -/
def vo (X : Exec) (e : EvId) : Nat := voG X X.gmo e

/-! ## 3. Observations -/

/-- THE REFERENCE ROW of hart `h`: the bytes each of its load operations returns, in program order. -/
def refRow (X : Exec) (h : Nat) : List (List Nat) :=
  (((X.evs[h]?).getD []).filter (fun v => v.sk.kind.isLoad)).map Ev.rdat

/-- The value of the `k`-th load of hart `h` (the reference counterpart of `PFRun.obsLoad`). -/
def refObsLoad (X : Exec) (h k : Nat) : Option Nat := ((refRow X h)[k]?).map bytesVal

/-- `sz` bytes of the final memory at `a`, little-endian (the reference counterpart of `finalMem`). -/
def refFinalMem (X : Exec) (a sz : Nat) : Nat := bytesVal ((List.range sz).map (fun k => finalByte X (a + k)))

/-- THE MACHINE ROW of a trace: the answered bytes of each load-like entry, in order (timestamps forgotten). -/
def machRow (τ : PF.Trace) : List (List Nat) := (PF.loadsOf τ).map (fun tvs => tvs.map (fun tv => tv.2.toNat))

/-- A run is PROMISES-FIRST (plan §0 `run'.promisesFirst`): its promise events precede its state events. -/
def promisesFirst (evs : List PEvt) : Prop :=
  ∃ k, (∀ e ∈ evs.take k, e.isSt = false) ∧ ∀ e ∈ evs.drop k, e.isSt = true

/-! ## 4. Pulte's `sim_view` -/

/-- `domF f P v` (Pulte `sim_view`): `v` is `0`, or at most `f j` for some `j` with `P j`. -/
def domF (f : Nat → Nat) (P : Nat → Prop) (v : Nat) : Prop := v = 0 ∨ ∃ j, P j ∧ v ≤ f j

theorem domF_zero (f : Nat → Nat) (P : Nat → Prop) : domF f P 0 := .inl rfl

theorem domF_of (f : Nat → Nat) {P : Nat → Prop} {v : Nat} (j : Nat) (hj : P j) (hv : v ≤ f j) : domF f P v :=
  .inr ⟨j, hj, hv⟩

theorem domF_le {f : Nat → Nat} {P : Nat → Prop} {v w : Nat} (h : domF f P w) (hvw : v ≤ w) : domF f P v := by
  rcases h with h | ⟨j, hj, hw⟩
  · exact .inl (by omega)
  · exact .inr ⟨j, hj, by omega⟩

theorem domF_mono {f : Nat → Nat} {P Q : Nat → Prop} {v : Nat} (h : domF f P v) (hPQ : ∀ j, P j → Q j) :
    domF f Q v := by
  rcases h with h | ⟨j, hj, hw⟩
  · exact .inl h
  · exact .inr ⟨j, hPQ j hj, hw⟩

theorem domF_max {f : Nat → Nat} {P : Nat → Prop} {v w : Nat} (hv : domF f P v) (hw : domF f P w) :
    domF f P (max v w) := by
  rcases Nat.le_total v w with h | h
  · rw [Nat.max_eq_right h]; exact hw
  · rw [Nat.max_eq_left h]; exact hv

theorem domF_bound {f : Nat → Nat} {P : Nat → Prop} {v B : Nat} (h : domF f P v) (hB : ∀ j, P j → f j ≤ B) :
    v ≤ B := by
  rcases h with h | ⟨j, hj, hw⟩
  · omega
  · exact Nat.le_trans hw (hB j hj)

theorem domF_lt {f : Nat → Nat} {P : Nat → Prop} {v B : Nat} (h : domF f P v) (hB : ∀ j, P j → f j < B)
    (h0 : 0 < B) : v < B := by
  rcases h with h | ⟨j, hj, hw⟩
  · omega
  · exact Nat.lt_of_le_of_lt hw (hB j hj)

/-! ## 5. The memory and the views (Pulte AtoP.v:26–147) -/

section memview

variable (X : Exec)

theorem memG_nil : memG X [] = [] := rfl

theorem memG_cons (x : EvId) (t : List EvId) :
    memG X (x :: t) = if isSt X x then msgOf X x :: memG X t else memG X t := by
  unfold memG
  by_cases h : isSt X x = true
  · simp [h]
  · simp [h]

theorem stCnt_le (x : EvId) : stCnt X x ≤ 1 := by unfold stCnt; split <;> omega

theorem stCnt_st {x : EvId} (h : isSt X x = true) : stCnt X x = 1 := by simp [stCnt, h]

theorem stCnt_nst {x : EvId} (h : isSt X x = false) : stCnt X x = 0 := by simp [stCnt, h]

theorem len_memG_cons (x : EvId) (t : List EvId) : (memG X (x :: t)).length = stCnt X x + (memG X t).length := by
  rw [memG_cons]
  unfold stCnt
  split <;> simp <;> omega

/-- Every view is at most the memory's length. -/
theorem voG_le_len : ∀ (g : List EvId) (e : EvId), voG X g e ≤ (memG X g).length
  | [], _ => Nat.zero_le _
  | x :: t, e => by
    rw [len_memG_cons]
    unfold voG
    split
    · omega
    · have := voG_le_len t e; omega

/-- A store of `g` has view `≥ 1`. -/
theorem voG_st_pos : ∀ (g : List EvId) (w : EvId), w ∈ g → isSt X w = true → 1 ≤ voG X g w
  | [], _, hw, _ => absurd hw (List.not_mem_nil)
  | x :: t, w, hw, hs => by
    unfold voG
    by_cases hx : x = w
    · subst hx; rw [if_pos rfl, stCnt_st X hs]; exact Nat.le_refl 1
    · rw [if_neg hx]
      have hwt : w ∈ t := by
        rcases List.mem_cons.1 hw with h | h
        · exact absurd h.symm hx
        · exact h
      have := voG_st_pos t w hwt hs; omega

/-- A STORE'S VIEW IS ITS TIMESTAMP: `memG g` holds its message at `voG g w`. -/
theorem memG_voG : ∀ (g : List EvId) (w : EvId), w ∈ g → isSt X w = true →
    (memG X g)[voG X g w - 1]? = some (msgOf X w)
  | [], _, hw, _ => absurd hw (List.not_mem_nil)
  | x :: t, w, hw, hs => by
    unfold voG
    rw [memG_cons]
    by_cases hx : x = w
    · subst hx; rw [if_pos rfl, stCnt_st X hs, if_pos hs]; rfl
    · rw [if_neg hx]
      have hwt : w ∈ t := by
        rcases List.mem_cons.1 hw with h | h
        · exact absurd h.symm hx
        · exact h
      have hpos := voG_st_pos X t w hwt hs
      have ih := memG_voG t w hwt hs
      by_cases hxs : isSt X x = true
      · rw [if_pos hxs, stCnt_st X hxs]
        obtain ⟨k, hk⟩ : ∃ k, voG X t w = k + 1 := ⟨voG X t w - 1, by omega⟩
        rw [hk] at ih ⊢
        simpa using ih
      · rw [if_neg hxs, stCnt_nst X (by simpa using hxs)]
        simpa using ih

/-- EVERY MESSAGE IS A STORE'S: each timestamp `1 ≤ t ≤ |memG g|` is the view of a store of `g`. -/
theorem voG_surj : ∀ (g : List EvId), g.Nodup → ∀ t, 1 ≤ t → t ≤ (memG X g).length →
    ∃ w, w ∈ g ∧ isSt X w = true ∧ voG X g w = t
  | [], _, t, h1, h2 => by simp [memG_nil] at h2; omega
  | x :: g', hn, t, h1, h2 => by
    have hnd := List.nodup_cons.1 hn
    rw [len_memG_cons] at h2
    by_cases hxs : isSt X x = true
    · rw [stCnt_st X hxs] at h2
      by_cases ht : t = 1
      · subst ht
        refine ⟨x, List.mem_cons_self .., hxs, ?_⟩
        unfold voG; rw [if_pos rfl, stCnt_st X hxs]
      · obtain ⟨w, hw, hws, hv⟩ := voG_surj g' hnd.2 (t - 1) (by omega) (by omega)
        have hne : x ≠ w := fun h => hnd.1 (h ▸ hw)
        refine ⟨w, List.mem_cons_of_mem _ hw, hws, ?_⟩
        unfold voG; rw [if_neg hne, stCnt_st X hxs, hv]; omega
    · rw [stCnt_nst X (by simpa using hxs)] at h2
      obtain ⟨w, hw, hws, hv⟩ := voG_surj g' hnd.2 t h1 (by omega)
      have hne : x ≠ w := fun h => hxs (h ▸ hws)
      refine ⟨w, List.mem_cons_of_mem _ hw, hws, ?_⟩
      unfold voG; rw [if_neg hne, stCnt_nst X (by simpa using hxs), hv]; omega

/-- VIEWS FOLLOW THE ORDER (Pulte `view_of_eid_ob`, `view_of_eid_ob_write`): an earlier event has a view at most
the later one's, strictly below it when the later one is a store. -/
theorem voG_pos_mono : ∀ (g : List EvId) (a b : EvId), a ∈ g → b ∈ g → pos g a < pos g b →
    voG X g a ≤ voG X g b ∧ (isSt X b = true → voG X g a < voG X g b)
  | [], _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: t, a, b, ha, hb, hp => by
    have hxb : x ≠ b := by
      intro h; subst h; rw [pos_cons_self] at hp; omega
    have hbt : b ∈ t := by
      rcases List.mem_cons.1 hb with h | h
      · exact absurd h.symm hxb
      · exact h
    by_cases hxa : x = a
    · subst hxa
      unfold voG
      rw [if_pos rfl, if_neg hxb]
      refine ⟨by omega, fun hs => ?_⟩
      have := voG_st_pos X t b hbt hs
      omega
    · have hat : a ∈ t := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hxa
        · exact h
      rw [pos_cons_ne _ _ _ hxa, pos_cons_ne _ _ _ hxb] at hp
      obtain ⟨h1, h2⟩ := voG_pos_mono t a b hat hbt (by omega)
      unfold voG
      rw [if_neg hxa, if_neg hxb]
      exact ⟨by omega, fun hs => by have := h2 hs; omega⟩

theorem voG_mono (g : List EvId) (a b : EvId) (h : gB g a b = true) :
    voG X g a ≤ voG X g b ∧ (isSt X b = true → voG X g a < voG X g b) := by
  obtain ⟨ha, hb, hp⟩ := gB_mem g a b h
  exact voG_pos_mono X g a b ha hb hp

/-- `g[pos g a] = a` for a member. -/
theorem getElem?_pos : ∀ (g : List EvId) (a : EvId), a ∈ g → g[pos g a]? = some a
  | [], _, ha => absurd ha (List.not_mem_nil)
  | x :: t, a, ha => by
    by_cases hx : x = a
    · subst hx; rw [pos_cons_self]; rfl
    · rw [pos_cons_ne _ _ _ hx]
      have hat : a ∈ t := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h.symm hx
        · exact h
      simpa using getElem?_pos t a hat

theorem pos_inj (g : List EvId) (a b : EvId) (ha : a ∈ g) (hb : b ∈ g) (h : pos g a = pos g b) : a = b := by
  have h1 := getElem?_pos g a ha
  have h2 := getElem?_pos g b hb
  rw [h] at h1
  rw [h1] at h2
  exact Option.some.inj h2

/-- Two members of `g` are equal or ordered one way or the other. -/
theorem gB_total (g : List EvId) (a b : EvId) (ha : a ∈ g) (hb : b ∈ g) :
    a = b ∨ gB g a b = true ∨ gB g b a = true := by
  rcases Nat.lt_trichotomy (pos g a) (pos g b) with h | h | h
  · right; left; simp [gB, ha, hb, h]
  · left; exact pos_inj g a b ha hb h
  · right; right; simp [gB, ha, hb, h]

/-- A STORE WHOSE VIEW IS AT MOST AN EVENT'S IS gmo-BEFORE IT (or is it). -/
theorem gB_of_voG_le (g : List EvId) (w e : EvId) (hw : w ∈ g) (hws : isSt X w = true) (he : e ∈ g)
    (hle : voG X g w ≤ voG X g e) (hne : w ≠ e) : gB g w e = true := by
  rcases gB_total g w e hw he with h | h | h
  · exact absurd h hne
  · exact h
  · have := (voG_mono X g e w h).2 hws; omega

/-- Views are injective on stores. -/
theorem voG_inj (g : List EvId) (w1 w2 : EvId) (h1 : w1 ∈ g) (h2 : w2 ∈ g) (hs1 : isSt X w1 = true)
    (hs2 : isSt X w2 = true) (h : voG X g w1 = voG X g w2) : w1 = w2 := by
  rcases gB_total g w1 w2 h1 h2 with e | e | e
  · exact e
  · have := (voG_mono X g w1 w2 e).2 hs2; omega
  · have := (voG_mono X g w2 w1 e).2 hs1; omega

/-- The message at a store's timestamp, in `memG`'s terms of `getElem?` at `t - 1`. -/
theorem memG_at (g : List EvId) (hn : g.Nodup) (t : Nat) (h1 : 1 ≤ t) (h2 : t ≤ (memG X g).length) :
    ∃ w, w ∈ g ∧ isSt X w = true ∧ voG X g w = t ∧ (memG X g)[t - 1]? = some (msgOf X w) := by
  obtain ⟨w, hw, hws, hv⟩ := voG_surj X g hn t h1 h2
  exact ⟨w, hw, hws, hv, hv ▸ memG_voG X g w hw hws⟩

end memview

end Weak.Prom.Cmp
