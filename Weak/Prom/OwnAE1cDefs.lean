/-
Weak/Prom: **E-a, G4 (1c) with the DEAD SET EMPTY — the protocol, per-byte owners, the lock steps** (stage E-a;
G4-review.md §6 condition 1: "re-prove (1c) and (4) on (a) with the dead set empty (per-byte pend ownership instead
of free mode)"; plan rev 7 §3 "Acquire", "Atomicity", "The deposit", "Opening", "Points-to", R-a1, R-a5).

The text and the test are (1c)'s (OwnALock1cDefs.lean, reused: `p1c`, `t1c`, `wL1c`).  What changes:
* NO DEAD SET.  The adequacy runs at `Dd := fun _ => False`; no `deadInv`, no free mode.
* PER-BYTE OWNERS (OwnAEBase.lean): every message touching the lock word `Lk..Lk+3` (`isLT`, whatever its shape,
  author or content) is the LOCK's: an acquire AMO (`C.isA`) → its author's own-message bag, a release-shaped word
  (`C.isR`) → its release slot, anything else (`isJE`) → `lkJunk` (the lock protocol keeps its `pend`: no lock
  operation writes it).  Every other message touching a counter byte (`isCT`) is the COUNTER's points-to's (any
  shape, any author: a 1-byte write by anybody included); every other message touching a cpu-field byte (`isPT`)
  is the cpu field's bag; the rest is the boot owner's (kept, never used).
* THE PROTOCOL `π1c` (the core's ⟦t⟧ facts, plan §2): a message touching the lock word is a 4-byte message at
  `Lk`.  Every text store meets it outright.  It is used ONCE: a counter read whose byte comes from a message that
  touches both the counter and the lock word (owned by the lock, so not in the reader's bag) gets the guarded fact
  `⟦t⟧ False` (`straddle_grd`) instead of a doom — a pure, LOCAL refutation that keeps every resource.
The lock steps (copies of OwnALock1cLib.lean's, free mode removed): a lock-word byte read below the frontier came from
the image, an acquire or a release — a junk source is FULFILLED (frontier), and its slot still holds its `pend`.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAEBase

namespace Weak.Prom.OA.EC

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open Weak.Prom.OA.C (Pc p1c b1c t1c xs1c xOf_1c p1c_at wL1c msgAt_of)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The protocol -/

/-- **THE PROTOCOL of (1c)** (plan §0 `Proto`): a message touching the lock word is a 4-byte message at `Lk`. -/
def π1c : Proto := ⟨fun m => tchB m Lk 4 = true → m.pa = Lk ∧ m.data.length = 4, fun _ => True⟩

theorem ok_lk {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 4) :
    π1c.okMsg ⟨Lk, d, tid, c⟩ := fun _ => ⟨rfl, hd⟩

theorem ok_far {m : PMsg} (h : m.pa + m.data.length ≤ Lk ∨ Lk + 4 ≤ m.pa) : π1c.okMsg m := fun ht => by
  rw [tchB_far h] at ht; cases ht

theorem ok_ct {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} : π1c.okMsg ⟨Ct, d, tid, c⟩ :=
  ok_far (.inr (by simp [Lk, Ct, X, Y]))

theorem ok_pc {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} : π1c.okMsg ⟨Pc, d, tid, c⟩ :=
  ok_far (.inr (by simp [Pc, Lk, X]))

/-- **THE GUARDED REFUTATION** (the core's ⟦t⟧, `grd_self`): a message that touches the lock word AND a counter byte
violates `π1c`, so `⟦t⟧ False`. -/
theorem straddle_grd {img : Image} {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m)
    (hL : tchB m Lk 4 = true) (hj : j < 8) (hb : (m.byteAt (Ct + j)).isSome = true) : grd π1c img M t False :=
  grd_imp (fun hok => by
    obtain ⟨hp, hl⟩ := hok hL
    have := byteAt_in hp hl hb
    simp only [Lk, Ct, X, Y] at this; omega) (grd_self hm)

/-! ## 2. Owners -/

/-- The lock's: touches the lock word. -/
def isLT (M : List PMsg) (t : Nat) : Bool := clsB (fun m => tchB m Lk 4 = true) M t
/-- The counter's: touches a counter byte, not the lock word. -/
def isCT (M : List PMsg) (t : Nat) : Bool := clsB (fun m => tchB m Ct 8 = true) M t && !isLT M t
/-- The cpu field's: touches a cpu-field byte, neither the lock word nor the counter. -/
def isPT (M : List PMsg) (t : Nat) : Bool :=
  clsB (fun m => tchB m Pc 8 = true) M t && !isLT M t && !isCT M t
/-- The lock's junk: touches the lock word, neither an acquire nor a release word. -/
def isJE (M : List PMsg) (t : Nat) : Bool := isLT M t && !C.isA M t && !C.isR M t

theorem wr_LT {M : List PMsg} {t j : Nat} (hj : j < 4) (h : wrB M (Lk + j) t) : isLT M t = true := by
  obtain ⟨m, hm, hb⟩ := h
  rw [isLT, clsB_of hm]; exact decide_eq_true (tchB_of hj hb)

theorem A_LT {M : List PMsg} {t : Nat} (h : C.isA M t = true) : isLT M t = true := by
  obtain ⟨m, hm, ⟨h1, h2, _⟩, _⟩ := clsB_iff.1 h
  exact wr_LT (j := 0) (by decide) ⟨m, hm, by
    rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl⟩

theorem R_LT {M : List PMsg} {t : Nat} (h : C.isR M t = true) : isLT M t = true := by
  obtain ⟨m, hm, ⟨h1, h2, _⟩, _⟩ := clsB_iff.1 h
  exact wr_LT (j := 0) (by decide) ⟨m, hm, by
    rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl⟩

/-- A lock-owned message is an acquire, a release, or junk. -/
theorem lt_cls {M : List PMsg} {t : Nat} (h : isLT M t = true) :
    C.isA M t = true ∨ C.isR M t = true ∨ isJE M t = true := by
  unfold isJE; rw [h]; cases C.isA M t <;> cases C.isR M t <;> simp

/-- A counter byte's writer: the counter's, or a message that also touches the lock word. -/
theorem wrC_cases {M : List PMsg} {t j : Nat} (hj : j < 8) (h : wrB M (Ct + j) t) :
    isCT M t = true ∨ ∃ m, msgAt M t = some m ∧ tchB m Lk 4 = true ∧ (m.byteAt (Ct + j)).isSome = true := by
  obtain ⟨m, hm, hb⟩ := h
  cases hL : isLT M t
  · left; rw [isCT, clsB_of hm, hL]; simp only [Bool.not_false, Bool.and_true]; exact decide_eq_true (tchB_of hj hb)
  · right; rw [isLT, clsB_of hm] at hL; exact ⟨m, hm, of_decide_eq_true hL, hb⟩

/-- A text-shaped counter message (`isC`) is the counter's. -/
theorem C_CT {M : List PMsg} {t : Nat} (h : isC M t = true) : isCT M t = true := by
  obtain ⟨m, hm, h1, h2, _⟩ := clsB_iff.1 h
  have hL : isLT M t = false := by
    rw [isLT, clsB_of hm]; simp only [decide_eq_false_iff_not]
    rw [tchB_far (by rw [h1, h2]; simp [Lk, Ct, X, Y])]; simp
  rw [isCT, clsB_of hm, hL]; simp only [Bool.not_false, Bool.and_true]
  refine decide_eq_true (tchB_of (j := 0) (by decide) ?_)
  rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

/-- The text's cpu-field store is the cpu field's. -/
theorem P_PT {M : List PMsg} {ts h : Nat} {d : List (BitVec 8)} (hd : d.length = 8) (h1 : 1 ≤ ts)
    (hm : M[ts - 1]? = some ⟨Pc, d, some h, .plain⟩) : isPT M ts = true := by
  have hmt := msgAt_of h1 hm
  have hL : isLT M ts = false := by
    rw [isLT, clsB_of hmt]; simp only [decide_eq_false_iff_not]
    rw [tchB_far (by simp [Pc, Lk, X])]; simp
  have hC : isCT M ts = false := by
    rw [isCT, clsB_of hmt, hL]; simp only [Bool.not_false, Bool.and_true, decide_eq_false_iff_not]
    rw [tchB_far (by simp [hd, Pc, Lk, Ct, X, Y])]; simp
  rw [isPT, clsB_of hmt, hL, hC]; simp only [Bool.not_false, Bool.and_true]
  exact decide_eq_true (tchB_of (j := 0) (by decide)
    (by rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [hd]; decide)]; rfl))

/-! ## 3. Bags and resources -/

def cBagE (M : List PMsg) (lw : Nat) : List Nat := (rng M).filter (fun t => decide (lw < t) && isCT M t)
def cBagXE (M : List PMsg) (lw ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lw < t) && decide (t ≠ ex) && isCT M t)
def pBagE (M : List PMsg) (s : Nat) : List Nat := (rng M).filter (fun t => decide (s < t) && isPT M t)

theorem cBagE_X (M : List PMsg) (lw : Nat) : cBagE M lw = cBagXE M lw 0 := by
  unfold cBagE cBagXE
  refine List.filter_congr (fun t ht => ?_)
  have := rng_ge ht
  simp [show t ≠ 0 by omega]

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- **THE COUNTER'S POINTS-TO, PER BYTE**: latest write `lw` (a text-shaped counter message, or the image), and the
`pend` of EVERY later message touching a counter byte that the lock does not own. -/
def cPtsE (g : AGN) (M : List PMsg) (lw : Nat) : IProp GF :=
  iprop(⌜lw = 0 ∨ isC M lw = true⌝ ∗ [∗list] t ∈ cBagE M lw, pend g t)

/-- The cpu field's bag above `s` (every message touching it that is not the lock's or the counter's). -/
def pPtsE (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop([∗list] t ∈ pBagE M s, pend g t)

/-- The lock's resource deposited at `s`. -/
def RsE (g : AGN) (M : List PMsg) (s : Nat) : IProp GF := iprop((∃ lw, ⌜lw ≤ s⌝ ∗ cPtsE g M lw) ∗ pPtsE g M s)

def lkNE : Namespace := ndot nroot "promLockE"

def iSlotE (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  inv (ndot lkNE 0) iprop(RsE g M 0 ∨ nxtTok M tk 0)

def rSlotE (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : IProp GF :=
  inv (ndot lkNE r) iprop(pend g r ∨ (shot g r ∗ token (tk r) ∗ (RsE g M r ∨ nxtTok M tk r)))

/-- THE LOCK PROTOCOL'S PERSISTENT PART: the image's slot, the release slots, the junk slots. -/
def lkCtxE (g : AGN) (M : List PMsg) (tk : Nat → GName) : IProp GF :=
  iprop(doomInv g M ∗ iSlotE g M tk ∗ ([∗list] r ∈ (rng M).filter (C.isR M), rSlotE g M tk r) ∗
    ([∗list] d ∈ (rng M).filter (isJE M), lkJunk g d))

instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (iSlotE (GF := GF) g M tk) := by
  unfold iSlotE; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) (r : Nat) : Persistent (rSlotE (GF := GF) g M tk r) := by
  unfold rSlotE; infer_instance
instance (g : AGN) (M : List PMsg) (tk : Nat → GName) : Persistent (lkCtxE (GF := GF) g M tk) := by
  unfold lkCtxE; infer_instance
instance (g : AGN) (M : List PMsg) (lw : Nat) : Timeless (cPtsE (GF := GF) g M lw) := by
  unfold cPtsE
  have : Timeless ([∗list] t ∈ cBagE M lw, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance
instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (pPtsE (GF := GF) g M s) := by
  unfold pPtsE; exact BigSepL.bigSepL_timeless (fun _ => inferInstance)
instance (g : AGN) (M : List PMsg) (s : Nat) : Timeless (RsE (GF := GF) g M s) := by unfold RsE; infer_instance

theorem pPtsE_mono (g : AGN) (M : List PMsg) {s s' : Nat} (h : s ≤ s') : pPtsE (GF := GF) g M s ⊢ pPtsE g M s' := by
  unfold pPtsE pBagE
  exact bsl_filter_mono (pend g) _ _ (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨by omega, ht.2⟩) (rng M)

theorem pPtsE_take (g : AGN) (M : List PMsg) {sp ts : Nat} (hlt : sp < ts) (hP : isPT M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) : pPtsE (GF := GF) g M sp ⊢ pend g ts ∗ pPtsE g M ts := by
  unfold pPtsE pBagE
  exact bsl_filter_take (pend g) (fun t => decide (sp < t) && isPT M t) (fun t => decide (ts < t) && isPT M t) ts
    (by simp [hP, hlt])
    (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M)

/-! ## 4. The lock steps (free mode removed) -/

/-- A junk lock message below the frontier is absurd. -/
theorem lkJ_front (g : AGN) (M : List PMsg) (tk : Nat → GName) (hdd : g.dd = fun _ => False) {π : Proto}
    {img : Image} {ws1 : PState} {v : Nat} (hvM : 1 ≤ v ∧ v ≤ M.length) (hv : v ≤ wfr ws1)
    (hJ : isJE M v = true) : lkCtxE (GF := GF) g M tk ∗ frontA g π img M ws1 ⊢ |={⊤}=> False := by
  iintro ⟨#Hctx, #Hfr⟩
  unfold lkCtxE
  icases Hctx with ⟨Hdoom, -, -, Hjs⟩
  ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hjs
  imod frontS g M hdd (π := π) (img := img) (ws := ws1) v ⟨hvM.1, hvM.2, hv⟩ $$ [] with #Hs
  · iframe Hdoom Hfr
  iapply junk_shot g v; iframe Hj Hs

/-- **A LOCK-WORD BYTE READ BELOW THE FRONTIER** came from the image, an acquire or a release. -/
theorem lk_srcE (g : AGN) (M : List PMsg) (tk : Nat → GName) (hdd : g.dd = fun _ => False) {π : Proto}
    {img : Image} {ws1 : PState} {t j : Nat} {v : BitVec 8} (hj : j < 4) (hb : memByte img M t (Lk + j) = some v)
    (ht : t ≤ wfr ws1) :
    lkCtxE (GF := GF) g M tk ∗ frontA g π img M ws1 ⊢ |={⊤}=> ⌜t = 0 ∨ C.isA M t = true ∨ C.isR M t = true⌝ := by
  iintro ⟨#Hctx, #Hfr⟩
  cases t with
  | zero => imodintro; ipureintro; exact .inl rfl
  | succ k =>
    obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    rcases lt_cls (wr_LT hj ⟨m, hmt, by rw [hba]; rfl⟩) with hA | hR | hJ
    · imodintro; ipureintro; exact .inr (.inl hA)
    · imodintro; ipureintro; exact .inr (.inr hR)
    · imod lkJ_front g M tk hdd (msgAt_le hmt) ht hJ $$ [] with %hf
      · iframe Hctx Hfr
      exact hf.elim

/-- **THE ATOMICITY STEP** (as OwnALock1cLib.lean's `lk_chain`): an AMO at `ts` that read byte `Lk` from `s0` has
`nxtL M s0 ts` — a lock-word write in between is the hart's own (atomicity) above its coherence floor (coherence):
an own acquire (`pend` in the bag), an own release (token in the bag), or junk — fulfilled (frontier), absurd. -/
theorem lk_chainE (g : AGN) (M : List PMsg) (tk : Nat → GName) (hdd : g.dd = fun _ => False) {π : Proto}
    {img : Image} {ws1 ws : PState} {h lo s0 ts vpre : Nat} (hs0 : s0 < ts) (hts : ts ≤ wfr ws1)
    (hwts : wrB M Lk ts) (hlo : lo ≤ coh ws Lk) (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) :
    lkCtxE (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ C.obag g M tk h lo ts ⊢
      |={⊤}=> C.obag g M tk h lo ts ∗ ⌜nxtL M s0 ts⌝ := by
  iintro ⟨#Hctx, #Hfr, Hbag⟩
  by_cases hn : nxtL M s0 ts
  · imodintro; iframe Hbag; ipureintro; exact hn
  have hex : ∃ v, s0 < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hs0, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, hwv⟩ := hex
  have hvM : 1 ≤ v ∧ v ≤ M.length := by obtain ⟨m, hm, _⟩ := hwv; exact msgAt_le hm
  have htid : tidAt M v = some h := by
    apply Classical.byContradiction; intro hne
    exact chain_excl hv1 hv2 hwv hne hx
  have hvl : lo < v := by
    apply Classical.byContradiction; intro hle
    exact chain_coh hv1 (by omega) hwv hr
  have hbyH : byH M h v = true := by simp [byH, htid]
  have hwv0 : wrB M (Lk + (0 : Nat)) v := by simpa using hwv
  ihave #Hctx' := Hctx
  unfold lkCtxE
  icases Hctx with ⟨Hdoom, -, Hrs, -⟩
  imod frontS g M hdd (π := π) (img := img) (ws := ws1) v ⟨hvM.1, hvM.2, by omega⟩ $$ [] with #Hsh
  · iframe Hdoom Hfr
  rcases lt_cls (wr_LT (by omega) hwv0) with hA | hR | hJ
  · unfold C.obag
    icases Hbag with ⟨HbA, -⟩
    unfold C.bagA
    icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && C.isA M t && byH M h t)
      (fun _ => false) v (by simp [hvl, show v ≠ ts by omega, hA, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbA with ⟨Hp, -⟩
    iexfalso; iapply pend_shot; iframe Hp Hsh
  · unfold C.obag
    icases Hbag with ⟨-, HbL⟩
    unfold C.bagL
    icases bsl_filter_take (fun t => token (tk t))
      (fun t => decide (lo < t) && decide (t ≠ ts) && (C.isA M t || C.isR M t) && byH M h t) (fun _ => false) v
      (by simp [hvl, show v ≠ ts by omega, hR, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbL with ⟨Ht, -⟩
    ihave #Hslot := bsl_mem (F := fun r => rSlotE g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hvM, hR⟩) $$ Hrs
    unfold rSlotE
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, -⟩
    icases Hb with (Hp | ⟨_, Ht', _⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · iexfalso; iapply token_exclusive; iframe Ht Ht'
  · imod lkJ_front g M tk hdd (π := π) (img := img) (ws1 := ws1) hvM (by omega) hJ $$ [] with %hf
    · unfold lkCtxE; iframe Hctx' Hfr
    exact hf.elim

/-- **THE CLAIM**: the acquirer at `ts` (holding the token of `ts`), whose read source `s0` is the image or a release
with `nxtL M s0 ts`, takes `RsE s0`. -/
theorem lk_claimE (g : AGN) (M : List PMsg) (tk : Nat → GName) (hdd : g.dd = fun _ => False) {π : Proto}
    {img : Image} {ws1 : PState} {s0 ts : Nat} (hn : nxtL M s0 ts) (hs0 : s0 = 0 ∨ C.isR M s0 = true)
    (hts : ts ≤ wfr ws1) :
    lkCtxE (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ token (tk ts) ⊢ |={⊤}=> RsE g M s0 := by
  iintro ⟨#Hctx, #Hfr, Ht⟩
  unfold lkCtxE
  icases Hctx with ⟨Hdoom, Hi, Hrs, -⟩
  rcases hs0 with rfl | hR
  · unfold iSlotE
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hi with ⟨Hb, Hclose⟩
    icases Hb with (HR | Hn)
    · imod Hclose $$ [Ht] with -
      · iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
      imodintro; iexact HR
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Ht Ht'
  · have hsM : 1 ≤ s0 ∧ s0 ≤ M.length := by
      obtain ⟨m, hm, _⟩ := clsB_iff.1 hR; exact msgAt_le hm
    imod frontS g M hdd (π := π) (img := img) (ws := ws1) s0 ⟨hsM.1, hsM.2, by have := hn.1; omega⟩ $$ [] with #Hsh
    · iframe Hdoom Hfr
    ihave #Hslot := bsl_mem (F := fun r => rSlotE g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hsM, hR⟩) $$ Hrs
    unfold rSlotE
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
    icases Hb with (Hp | ⟨_, Ha, (HR | Hn)⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod Hclose $$ [Ht Ha] with -
      · iright; iframe Hsh Ha; iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
      imodintro; iexact HR
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- **THE ACQUIRE**: value `1` (held), or `0` with `RsE s0` for the read source `s0 < ts`. -/
theorem lk_acqE (g : AGN) (M : List PMsg) (tk : Nat → GName) (h : Nat) (hdd : g.dd = fun _ => False) {π : Proto}
    {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts lo vpre : Nat} (hlen : tvs.length = 4)
    (hlo1 : loadOk imgL M ws vpre Lk tvs) (hex : exclOk M h Lk (tvs.map Prod.fst) ts)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hlo : lo ≤ coh ws Lk) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    lkCtxE (GF := GF) g M tk ∗ frontA g π imgL M ws1 ∗ C.obag g M tk h lo ts ∗ token (tk ts) ⊢
      |={⊤}=> (C.obag g M tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 1 4⌝) ∨
        (C.obag g M tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗ ∃ s0, ⌜s0 < ts⌝ ∗ RsE g M s0) := by
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
  obtain ⟨_, hr0⟩ := loadOk_b0 hlo1
  have hr0 : ¬ writesIn M Lk t0 (max vpre (coh ws Lk)) := by
    rcases hr0 with h | ⟨ti, hci, _⟩
    · exact h
    · exact absurd hci (hnoinv _ _)
  imod lk_srcE g M tk hdd (ws1 := ws1) (π := π) (j := 0) (by decide) hb0 (by omega) $$ [] with %hc0
  · iframe Hctx Hfr
  imod lk_srcE g M tk hdd (ws1 := ws1) (π := π) (j := 1) (by decide) hb1 (by omega) $$ [] with %hc1
  · iframe Hctx Hfr
  imod lk_srcE g M tk hdd (ws1 := ws1) (π := π) (j := 2) (by decide) hb2 (by omega) $$ [] with %hc2
  · iframe Hctx Hfr
  imod lk_srcE g M tk hdd (ws1 := ws1) (π := π) (j := 3) (by decide) hb3 (by omega) $$ [] with %hc3
  · iframe Hctx Hfr
  have hword : [v0, v1, v2, v3] = toBytes (if C.isA M t0 = true then 1 else 0) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp)
      (C.lk_val (by decide) hb0 hc0) (C.lk_val (by decide) hb1 hc1) (C.lk_val (by decide) hb2 hc2)
      (C.lk_val (by decide) hb3 hc3)
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases hA0 : C.isA M t0 = true
  · rw [if_pos hA0] at hword
    imodintro; ileft; iframe Hbag; ipureintro; rw [hmap, hword]
  · rw [if_neg hA0] at hword
    have hc0' : t0 = 0 ∨ C.isR M t0 = true := by
      rcases hc0 with h | h | h
      · exact .inl h
      · exact absurd h hA0
      · exact .inr h
    imod lk_chainE g M tk hdd (ws1 := ws1) (ws := ws) (π := π) (h := h) (lo := lo) (s0 := t0) (ts := ts)
      (vpre := vpre) hs0 hts hwts hlo hr0 hex.1 $$ [Hbag] with ⟨Hbag, %hn⟩
    · iframe Hctx Hfr Hbag
    imod lk_claimE g M tk hdd (ws1 := ws1) (π := π) hn hc0' hts $$ [Htok] with HR
    · iframe Hctx Hfr Htok
    imodintro; iright; iframe Hbag
    isplitr
    · ipureintro; rw [hmap, hword]
    · iexists t0; iframe HR; ipureintro; omega

end res

end Weak.Prom.OA.EC
