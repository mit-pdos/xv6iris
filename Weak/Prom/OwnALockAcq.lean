/-
Weak/Prom: **G4 target (1a) on track (a): the acquire** (stage S4a part 2; plan rev 7 §3 "Acquire": "An aq AMO gives
`WF ≥ ts > tr` immediately … So the acquirer can open the source's invariant at once"; "Atomicity").

`lk_acq`: at the step after an acquiring AMO at `ts` (whose frontier is `≥ ts`), from the AMO's facts (`loadOk`,
`exclOk`, the coherence bounds) the read value is `1` (an acquire attempt's message: the lock is held), or `0` and
the acquirer holds `Rs s0` for its read source `s0 < ts` (the image or a release; `lk_chain` + `lk_claim`), or the
run is in free mode.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALockCS

namespace Weak.Prom.OA

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-- The byte a lock-word read returns, by its source's class. -/
theorem lk_val {M : List PMsg} {t j : Nat} {v : BitVec 8} (hj : j < 4) (hb : memByte imgL M t (Lk + j) = some v)
    (hc : t = 0 ∨ isA M t = true ∨ isR M t = true) :
    some v = (toBytes (if isA M t = true then 1 else 0) 4)[j]? := by
  rcases hc with rfl | hA | hR
  · simp only [memByte, imgL_zero] at hb
    cases hb
    have hA0 : isA M 0 = false := rfl
    rw [hA0]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> decide
  · obtain ⟨m, hm, hba⟩ : ∃ m, msgAt M t = some m ∧ m.byteAt (Lk + j) = some v := by
      cases t with
      | zero => cases hA
      | succ k =>
        obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
        exact ⟨m, by simpa [msgAt] using hm, hba⟩
    rw [if_pos hA, ← isA_byte hm hA hj, hba]
  · obtain ⟨m, hm, hba⟩ : ∃ m, msgAt M t = some m ∧ m.byteAt (Lk + j) = some v := by
      cases t with
      | zero => cases hR
      | succ k =>
        obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
        exact ⟨m, by simpa [msgAt] using hm, hba⟩
    have hA : isA M t = false := by
      cases h : isA M t
      · rfl
      · rw [isA_R h] at hR; cases hR
    rw [hA]; simp only [Bool.false_eq_true, if_false]
    rw [← isR_byte hm hR hj, hba]

/-- Four bytes by class: the word is `toBytes c 4` with `c` byte 0's. -/
theorem lk_word {v0 v1 v2 v3 : BitVec 8} {c0 c1 c2 c3 : Nat} (hc0 : c0 = 0 ∨ c0 = 1) (hc1 : c1 = 0 ∨ c1 = 1)
    (hc2 : c2 = 0 ∨ c2 = 1) (hc3 : c3 = 0 ∨ c3 = 1)
    (h0 : some v0 = (toBytes c0 4)[0]?) (h1 : some v1 = (toBytes c1 4)[1]?) (h2 : some v2 = (toBytes c2 4)[2]?)
    (h3 : some v3 = (toBytes c3 4)[3]?) : [v0, v1, v2, v3] = toBytes c0 4 := by
  have t0 : toBytes 0 4 = [0, 0, 0, 0] := by decide
  have t1 : toBytes 1 4 = [1, 0, 0, 0] := by decide
  rcases hc0 with rfl | rfl <;> rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
    rcases hc3 with rfl | rfl <;>
    simp only [t0, t1, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3 <;>
    subst h0 h1 h2 h3 <;> rfl

section acq

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE ACQUIRE** (see the header). -/
theorem lk_acq (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hdd : g.dd = ddL M) {π : Proto}
    {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts lo vpre : Nat} (hlen : tvs.length = 4)
    (hlo1 : loadOk imgL M ws vpre Lk tvs) (hex : exclOk M h Lk (tvs.map Prod.fst) ts)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hlo : lo ≤ coh ws Lk) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) :
    lkCtx (GF := GF) g M tk ∗ frontA g π imgL M ws1 ∗ obag g M tk h lo ts ∗ token (tk ts) ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ (obag g M tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 1 4⌝) ∨
        (obag g M tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗ ∃ lw, ⌜lw < ts⌝ ∗ cPts g M lw) := by
  iintro ⟨#Hctx, #Hfr, Hbag, Htok⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hw := loadOk_weak hlo1
  have hb : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte imgL M t (Lk + j) = some v ∧ t < ts := fun j t v hj hg =>
    ⟨(bytesAll_get hw hg).1, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj)⟩
  obtain ⟨hb0, hs0⟩ := hb 0 t0 v0 (by decide) rfl
  obtain ⟨hb1, hs1⟩ := hb 1 t1 v1 (by decide) rfl
  obtain ⟨hb2, hs2⟩ := hb 2 t2 v2 (by decide) rfl
  obtain ⟨hb3, hs3⟩ := hb 3 t3 v3 (by decide) rfl
  have hb0' : memByte imgL M t0 Lk = some v0 := by simpa using hb0
  obtain ⟨_, hr0⟩ := loadOk_b0 hlo1
  -- an invalidate on the path: dead, free mode
  rcases hr0 with hr0 | ⟨ti, hci, hti, _⟩
  rotate_left
  · obtain ⟨hJ, hD, hti2⟩ := cmo_dead (by omega) hci
    unfold lkCtx
    icases Hctx with ⟨Hdoom, -, -, Hdd⟩
    ihave #Hdi := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 ⟨by omega, hti2⟩, hJ⟩) $$ Hdd
    imod dead_doom g M ti ⟨by omega, hti2⟩ (by rw [hdd]; exact ⟨by omega, hD⟩) $$ [] with ⟨#Hf, #Hd⟩
    · iframe Hdoom Hdi
    imodintro; ileft; iframe Hf Hd
  -- the four sources' classes
  imod lk_src g M tk (ws1 := ws1) (π := π) (j := 0) (by decide) hb0 (by omega) $$ [] with (⟨#Hf, #Hd⟩ | %hc0)
  · iframe Hctx Hfr
  · imodintro; ileft; iframe Hf Hd
  imod lk_src g M tk (ws1 := ws1) (π := π) (j := 1) (by decide) hb1 (by omega) $$ [] with (⟨#Hf, #Hd⟩ | %hc1)
  · iframe Hctx Hfr
  · imodintro; ileft; iframe Hf Hd
  imod lk_src g M tk (ws1 := ws1) (π := π) (j := 2) (by decide) hb2 (by omega) $$ [] with (⟨#Hf, #Hd⟩ | %hc2)
  · iframe Hctx Hfr
  · imodintro; ileft; iframe Hf Hd
  imod lk_src g M tk (ws1 := ws1) (π := π) (j := 3) (by decide) hb3 (by omega) $$ [] with (⟨#Hf, #Hd⟩ | %hc3)
  · iframe Hctx Hfr
  · imodintro; ileft; iframe Hf Hd
  have hword : [v0, v1, v2, v3] = toBytes (if isA M t0 = true then 1 else 0) 4 := by
    have e1 := lk_val (by decide) hb1 hc1
    have e2 := lk_val (by decide) hb2 hc2
    have e3 := lk_val (by decide) hb3 hc3
    exact lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp)
      (lk_val (by decide) hb0 hc0) e1 e2 e3
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases hA0 : isA M t0 = true
  · rw [if_pos hA0] at hword
    imodintro; iright; ileft; iframe Hbag; ipureintro; rw [hmap, hword]
  · rw [if_neg hA0] at hword
    have hc0' : t0 = 0 ∨ isR M t0 = true := by
      rcases hc0 with h | h | h
      · exact .inl h
      · exact absurd h hA0
      · exact .inr h
    have hx0 : ¬ writesInBy M (fun tid => tid ≠ some h) Lk t0 (ts - 1) := hex.1
    imod lk_chain g M tk (ws1 := ws1) (ws := ws) (π := π) (h := h) (lo := lo) (s0 := t0) (ts := ts) (vpre := vpre)
      hs0 hts hwts hlo hr0 hx0 $$ [Hbag] with (⟨Hbag, %hn⟩ | ⟨#Hf, #Hd⟩)
    · iframe Hctx Hfr Hbag
    · imod lk_claim g M tk (ws1 := ws1) (π := π) hn hc0' hts $$ [Htok] with (⟨#Hf, #Hd⟩ | HR)
      · iframe Hctx Hfr Htok
      · imodintro; ileft; iframe Hf Hd
      · unfold Rs
        icases HR with ⟨%lw, %hlw, Hc⟩
        imodintro; iright; iright; iframe Hbag
        isplitr
        · ipureintro; rw [hmap, hword]
        · iexists lw; iframe Hc; ipureintro; omega
    · imodintro; ileft; iframe Hf Hd

end acq

end Weak.Prom.OA
