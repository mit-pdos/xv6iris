/-
Weak/Prom: **E-a, G4 (4) with the DEAD SET EMPTY — the protocol, per-byte owners, the two acquires** (stage E-a;
G4-review.md §6 condition 1; plan rev 7 §4 G4 (4), §3 "Lock birth and deferred deposits", "The rev-4 design",
"Acquire", "Atomicity", R-a4, R-a5).

The test, the texts, the saved-proposition birth slot `bSlot`, the handle `isLockAt` and the deferred deposit
`bslot_deposit` / claim `bslot_claim` are (4)'s (OwnAPipe*.lean, reused).  What changes:
* NO DEAD SET (`Dd := fun _ => False`), no free mode.
* PER-BYTE OWNERS FROM BOOT: the field `C` (`Ct..Ct+7`) and the L2 word (`Lk..Lk+3`) are bytes of hart 0's page
  (`kalloc`): hart 0 holds the `pend` of EVERY message touching them (`isCO`, `isL2O`: any shape, any author, any
  content — hart 1's future AMO writes and release of L2 included), the L2 ones with their claim tokens.  The L1
  word is the boot lock's (its protocol: hart 1's acquire AMOs `isK 2` to hart 1, hart 0's release words `isK 3` to
  their slots, anything else touching it to `lkJunk`).  The rest stays with its boot owner, unused.
* OWNERSHIP MOVES: hart 0 writes the junk and the birth `b` of L2 from its bags, initialises the field (`c`), and at
  its L1 release deposits the field's points-to in `b`'s saved-proposition slot (naming the runtime `γ`) and the
  L2 WORD'S BAG ABOVE `b` (`zBagE`, every later L2 message's `pend` and token) in L1's slot (`Pub1E`).
* THE L2 ACQUIRE (`l2_byteE`, R-a4 BY OWNERSHIP): hart 1's read lies above `lo` (the birth or its own last AMO
  write, `lo ≤` its view), so a byte's source is `lo` or a later L2-touching message — whose `pend` hart 1 holds
  (fulfilled by the frontier: absurd) or which also touches L1 (`lkJunk`: absurd).  No content classification of
  L2's messages, no `exclOk` argument: the atomicity `nxtL b ts` (`l2_nxtE`) is the same ownership fact.
* THE PROTOCOL `π4` (the core's ⟦t⟧): a message touching a lock word is a 4-byte message at that word; it refutes
  a field read from a lock-owned straddling message (`straddle4_grd`).
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAPipe
import Weak.Prom.OwnAEBase

namespace Weak.Prom.OA.EP

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 J p4o p4h b4o b4h t4 xs4 p4o_at p4h_at img4 w4 img4_L1 kind knd isK bth knd_of kind_2 kind_3
  kind_L1 kind_a1 kind_r1 kind_jk kind_bt bagK SV bN dpendD dshotD bSlot bthAt isLockAt cAt5 q4 qs4 q4_nil
  q4_snoc notCLd_st notCLd_rmw ownGF4 bslot_deposit bslot_claim l1_val tk1 bth_wr vals_of_src msgAt_of)
open Weak.Prom.OA.E
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 1. The protocol -/

/-- **THE PROTOCOL of (4)**: a message touching a lock word (L2 at `Lk`, L1) is a 4-byte message at that word. -/
def π4 : Proto :=
  ⟨fun m => (tchB m Lk 4 = true → m.pa = Lk ∧ m.data.length = 4) ∧
    (tchB m L1 4 = true → m.pa = L1 ∧ m.data.length = 4), fun _ => True⟩

theorem ok4_lk {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 4) :
    π4.okMsg ⟨Lk, d, tid, c⟩ :=
  ⟨fun _ => ⟨rfl, hd⟩, (fun ht => by rw [tchB_far (.inl (by simp [hd, Lk, L1, X, Z]))] at ht; cases ht)⟩

theorem ok4_l1 {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 4) :
    π4.okMsg ⟨L1, d, tid, c⟩ :=
  ⟨(fun ht => by rw [tchB_far (.inr (by simp [Lk, L1, X, Z]))] at ht; cases ht), fun _ => ⟨rfl, hd⟩⟩

theorem ok4_ct {d : List (BitVec 8)} {tid : Option Nat} {c : PClass} (hd : d.length = 8) :
    π4.okMsg ⟨Ct, d, tid, c⟩ :=
  ⟨(fun ht => by rw [tchB_far (.inr (by simp [Lk, Ct, X, Y]))] at ht; cases ht),
   (fun ht => by rw [tchB_far (.inl (by simp [hd, Ct, L1, Y, Z]))] at ht; cases ht)⟩

/-- **THE GUARDED REFUTATION**: a message touching a field byte and a lock word violates `π4`: `⟦t⟧ False`. -/
theorem straddle4_grd {img : Image} {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m)
    (hL : tchB m Lk 4 = true ∨ tchB m L1 4 = true) (hj : j < 8) (hb : (m.byteAt (Ct + j)).isSome = true) :
    grd π4 img M t False :=
  grd_imp (fun hok => by
    rcases hL with hL | hL
    · obtain ⟨hp, hl⟩ := hok.1 hL
      have := byteAt_in hp hl hb
      simp only [Lk, Ct, X, Y] at this; omega
    · obtain ⟨hp, hl⟩ := hok.2 hL
      have := byteAt_in hp hl hb
      simp only [L1, Ct, Z, Y] at this; omega) (grd_self hm)

/-! ## 2. Owners -/

def tL1 (M : List PMsg) (t : Nat) : Bool := clsB (fun m => tchB m L1 4 = true) M t
def tL2 (M : List PMsg) (t : Nat) : Bool := clsB (fun m => tchB m Lk 4 = true) M t
/-- The L2 word's (hart 0's page, then the lock's): touches L2, not L1. -/
def isL2O (M : List PMsg) (t : Nat) : Bool := tL2 M t && !tL1 M t
/-- The field's: touches a field byte, neither lock word. -/
def isCO (M : List PMsg) (t : Nat) : Bool := clsB (fun m => tchB m Ct 8 = true) M t && !tL1 M t && !tL2 M t
/-- L1's junk: touches L1, neither an acquire AMO (`isK 2`) nor a release word (`isK 3`). -/
def junk1 (M : List PMsg) (t : Nat) : Bool := tL1 M t && !isK M 2 t && !isK M 3 t

theorem tL1_of {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (L1 + j)).isSome = true) : tL1 M t = true := by
  rw [tL1, clsB_of hm]; exact decide_eq_true (tchB_of hj hb)

theorem tL2_of {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (Lk + j)).isSome = true) : tL2 M t = true := by
  rw [tL2, clsB_of hm]; exact decide_eq_true (tchB_of hj hb)

/-- A message at `p` with `n` bytes, far from `[a, a+4)`, does not touch it. -/
theorem tch_far_of {M : List PMsg} {t : Nat} {m : PMsg} (hm : msgAt M t = some m) {a : Int}
    (h : m.pa + m.data.length ≤ a ∨ a + 4 ≤ m.pa) : clsB (fun m => tchB m a 4 = true) M t = false := by
  rw [clsB_of hm]; simp only [decide_eq_false_iff_not]; rw [tchB_far h]; simp

/-- An L1 lock message (classes 2, 3) touches L1 only. -/
theorem k23_L1 {M : List PMsg} {t : Nat} (h : isK M 2 t = true ∨ isK M 3 t = true) :
    tL1 M t = true ∧ tL2 M t = false := by
  cases hmt : msgAt M t with
  | none => unfold isK knd at h; rw [hmt] at h; simp at h
  | some m =>
    have hpl : m.pa = L1 ∧ m.data.length = 4 := by
      unfold isK at h; rw [knd_of hmt] at h
      rcases h with h | h
      · have := kind_2 (of_decide_eq_true h); exact ⟨this.1, by rw [this.2.1]; rfl⟩
      · have := kind_3 (of_decide_eq_true h); exact ⟨this.1, by rw [this.2.1]; rfl⟩
    refine ⟨tL1_of hmt (j := 0) (by decide) ?_, ?_⟩
    · rw [← hpl.1, byteAt_off rfl, List.getElem?_eq_getElem (by rw [hpl.2]; decide)]; rfl
    · unfold tL2; exact tch_far_of hmt (.inr (by rw [hpl.1]; simp [Lk, L1, X, Z]))

/-- A source of an L1 byte: an L1 lock message, or L1's junk. -/
theorem l1_cls {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (L1 + j)).isSome = true) : isK M 2 t = true ∨ isK M 3 t = true ∨ junk1 M t = true := by
  have h1 := tL1_of hm hj hb
  unfold junk1; rw [h1]; cases isK M 2 t <;> cases isK M 3 t <;> simp

/-- A source of an L2 byte: the L2 word's, or L1's junk (a message touching both words). -/
theorem l2_cls {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 4)
    (hb : (m.byteAt (Lk + j)).isSome = true) : isL2O M t = true ∨ junk1 M t = true := by
  have h2 := tL2_of hm hj hb
  cases h1 : tL1 M t
  · left; simp [isL2O, h2, h1]
  · right
    have n2 : isK M 2 t = false := by
      cases h : isK M 2 t
      · rfl
      · rw [(k23_L1 (.inl h)).2] at h2; cases h2
    have n3 : isK M 3 t = false := by
      cases h : isK M 3 t
      · rfl
      · rw [(k23_L1 (.inr h)).2] at h2; cases h2
    simp [junk1, h1, n2, n3]

/-- A source of a field byte: the field's, or a message touching a lock word too. -/
theorem c_cls {M : List PMsg} {t j : Nat} {m : PMsg} (hm : msgAt M t = some m) (hj : j < 8)
    (hb : (m.byteAt (Ct + j)).isSome = true) :
    isCO M t = true ∨ (tchB m Lk 4 = true ∨ tchB m L1 4 = true) := by
  cases h1 : tL1 M t
  · cases h2 : tL2 M t
    · left; rw [isCO, clsB_of hm, h1, h2]; simp only [Bool.not_false, Bool.and_true]
      exact decide_eq_true (tchB_of hj hb)
    · right; left; rw [tL2, clsB_of hm] at h2; exact of_decide_eq_true h2
  · right; right; rw [tL1, clsB_of hm] at h1; exact of_decide_eq_true h1

/-- The text-shaped field message (`isC`) is the field's. -/
theorem C_CO {M : List PMsg} {t : Nat} (h : isC M t = true) : isCO M t = true := by
  obtain ⟨m, hm, h1, h2, _⟩ := clsB_iff.1 h
  have n1 : tL1 M t = false := tch_far_of hm (.inl (by rw [h1, h2]; simp [Ct, L1, Y, Z]))
  have n2 : tL2 M t = false := tch_far_of hm (.inr (by rw [h1]; simp [Lk, Ct, X, Y]))
  rw [isCO, clsB_of hm, n1, n2]; simp only [Bool.not_false, Bool.and_true]
  refine decide_eq_true (tchB_of (j := 0) (by decide) ?_)
  rw [← h1, byteAt_off rfl, List.getElem?_eq_getElem (by omega)]; rfl

/-- A 4-byte message at `Lk` is the L2 word's. -/
theorem lk_L2O {M : List PMsg} {t : Nat} {d : List (BitVec 8)} {tid : Option Nat} {c : PClass}
    (hd : d.length = 4) (hm : msgAt M t = some ⟨Lk, d, tid, c⟩) : isL2O M t = true := by
  have n1 : tL1 M t = false := tch_far_of hm (.inl (by simp [hd, Lk, L1, X, Z]))
  have h2 : tL2 M t = true := tL2_of hm (j := 0) (by decide) (by
    rw [byteAt_off rfl, List.getElem?_eq_getElem (by rw [hd]; decide)]; rfl)
  simp [isL2O, n1, h2]

/-! ## 3. Bags and resources -/

def zB (M : List PMsg) (lo ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lo < t) && decide (t ≠ ex) && isL2O M t)
def cB (M : List PMsg) (lw : Nat) : List Nat := (rng M).filter (fun t => decide (lw < t) && isCO M t)
def cBX (M : List PMsg) (lw ex : Nat) : List Nat :=
  (rng M).filter (fun t => decide (lw < t) && decide (t ≠ ex) && isCO M t)

theorem cB_X (M : List PMsg) (lw : Nat) : cB M lw = cBX M lw 0 := by
  unfold cB cBX
  refine List.filter_congr (fun t ht => ?_)
  have := rng_ge ht
  simp [show t ≠ 0 by omega]

def l1NE : Namespace := ndot nroot "promL1E"

section res

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-- **THE L2 WORD'S BAG above `lo`** (except `ex`): the `pend` and the claim token of every later message touching
it, whatever its shape or author. -/
def zBagE (g : AGN) (M : List PMsg) (sv : SV) (lo ex : Nat) : IProp GF :=
  iprop(([∗list] t ∈ zB M lo ex, pend g t) ∗ [∗list] t ∈ zB M lo ex, token (sv.tk t))

/-- **THE FIELD'S POINTS-TO, PER BYTE**: latest write `lw`, and the `pend` of every later message touching it. -/
def cPtsP (g : AGN) (M : List PMsg) (lw : Nat) : IProp GF :=
  iprop(⌜lw = 0 ∨ isC M lw = true⌝ ∗ [∗list] t ∈ cB M lw, pend g t)

/-- **L1's RESOURCE deposited at its release `s`**: the L2 handle (runtime `γ`, birth `b < s`, protecting the field's
points-to at `c < s` holding 5), and the L2 word's bag above `b`. -/
def Pub1E (g : AGN) (M : List PMsg) (sv : SV) (s : Nat) : IProp GF :=
  iprop(∃ γ b c, ⌜b < s ∧ c < s ∧ cAt5 M c⌝ ∗ isLockAt M sv γ Lk (cPtsP g M c) b ∗ zBagE g M sv b 0)

def l1SlotE (g : AGN) (M : List PMsg) (sv : SV) (t : Nat) : IProp GF :=
  inv (ndot l1NE t) iprop(pend g t ∨ (shot g t ∗ (Pub1E g M sv t ∨ token (sv.tk t))))

/-- THE PROTOCOL'S PERSISTENT PART: L1's release slots, the birth slots, L1's junk slots. -/
def pCtxE (g : AGN) (M : List PMsg) (sv : SV) : IProp GF :=
  iprop(doomInv g M ∗ ([∗list] t ∈ (rng M).filter (isK M 3), l1SlotE g M sv t) ∗
    ([∗list] t ∈ (rng M).filter (bth M), bSlot M sv t) ∗ ([∗list] t ∈ (rng M).filter (junk1 M), lkJunk g t))

instance (g : AGN) (M : List PMsg) (sv : SV) (t : Nat) : Persistent (l1SlotE (GF := GF) g M sv t) := by
  unfold l1SlotE; infer_instance
instance (g : AGN) (M : List PMsg) (sv : SV) : Persistent (pCtxE (GF := GF) g M sv) := by
  unfold pCtxE; infer_instance
instance (g : AGN) (M : List PMsg) (lw : Nat) : Timeless (cPtsP (GF := GF) g M lw) := by
  unfold cPtsP
  have : Timeless ([∗list] t ∈ cB M lw, pend (GF := GF) g t) := BigSepL.bigSepL_timeless (fun _ => inferInstance)
  infer_instance

theorem cPtsP_take (g : AGN) (M : List PMsg) {lw ts : Nat} (hlt : lw < ts) (hC : isC M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) : cPtsP (GF := GF) g M lw ⊢ pend g ts ∗ cPtsP g M ts := by
  unfold cPtsP cB
  iintro ⟨_, Hb⟩
  icases bsl_filter_take (pend g) (fun t => decide (lw < t) && isCO M t) (fun t => decide (ts < t) && isCO M t) ts
    (by simp [hlt, C_CO hC]) (fun t ht => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, ht.2⟩, by omega⟩)
    (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Hb with ⟨Hp, Hb⟩
  iframe Hp Hb; ipureintro; exact .inr hC

/-- Take `ts` (`pend` and token) out of the L2 bag; the bag above `ts` remains. -/
theorem zBag_takeE (g : AGN) (M : List PMsg) (sv : SV) {lo ts : Nat} (hlt : lo < ts) (hk : isL2O M ts = true)
    (htM : 1 ≤ ts ∧ ts ≤ M.length) :
    zBagE (GF := GF) g M sv lo 0 ⊢ (pend g ts ∗ token (sv.tk ts)) ∗ zBagE g M sv lo ts := by
  unfold zBagE zB
  iintro ⟨Hp, Ht⟩
  have hq : ∀ t, (decide (lo < t) && decide (t ≠ ts) && isL2O M t) = true →
      (decide (lo < t) && decide (t ≠ 0) && isL2O M t) = true ∧ t ≠ ts := fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨⟨ht.1.1, by omega⟩, ht.2⟩, ht.1.2⟩
  icases bsl_filter_take (pend g) _ (fun t => decide (lo < t) && decide (t ≠ ts) && isL2O M t) ts
    (by simp [hlt, hk]; omega) hq (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Hp with ⟨Hp1, Hp⟩
  icases bsl_filter_take (fun t => token (sv.tk t)) _ (fun t => decide (lo < t) && decide (t ≠ ts) && isL2O M t) ts
    (by simp [hlt, hk]; omega) hq (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Ht with ⟨Ht1, Ht⟩
  iframe Hp1 Ht1 Hp Ht

/-- The bag above `lo` except `ts` covers the bag above `ts`. -/
theorem zBag_up (g : AGN) (M : List PMsg) (sv : SV) {lo ts ex : Nat} (h : lo ≤ ts) (hex : ex ≤ ts) :
    zBagE (GF := GF) g M sv lo ex ⊢ zBagE g M sv ts 0 := by
  unfold zBagE zB
  have hm : ∀ t, (decide (ts < t) && decide (t ≠ 0) && isL2O M t) = true →
      (decide (lo < t) && decide (t ≠ ex) && isL2O M t) = true := fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨⟨by omega, by omega⟩, ht.2⟩
  iintro ⟨Hp, Ht⟩
  isplitl [Hp]
  · iapply bsl_filter_mono (pend g) _ _ hm (rng M) $$ Hp
  · iapply bsl_filter_mono (fun t => token (sv.tk t)) _ _ hm (rng M) $$ Ht

/-! ## 4. L1's slot -/

theorem l1_depositE (g : AGN) (M : List PMsg) (sv : SV) (r : Nat) :
    l1SlotE (GF := GF) g M sv r ∗ Pub1E g M sv r ⊢ |={⊤}=> shot g r := by
  iintro ⟨#Hs, HP⟩
  unfold l1SlotE
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (>Hp | ⟨>#Hsh, HB⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [HP] with -
    · inext; iright; iframe Hsh; ileft; iexact HP
    imodintro; iexact Hsh
  · imod Hclose $$ [HB] with -
    · inext; iright; iframe Hsh; iexact HB
    imodintro; iexact Hsh

theorem l1_claimE (g : AGN) (M : List PMsg) (sv : SV) (s : Nat) :
    l1SlotE (GF := GF) g M sv s ∗ shot g s ∗ token (sv.tk s) ∗ £ 1 ⊢ |={⊤}=> Pub1E g M sv s := by
  iintro ⟨#Hs, #Hsh, Ht, Hc⟩
  unfold l1SlotE
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot l1NE s))
      (P := iprop(pend g s ∨ (shot g s ∗ (Pub1E g M sv s ∨ token (sv.tk s)))))) $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, (HR | Ht')⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod Hclose $$ [Ht] with -
    · inext; iright; iframe Hsh; iright; iexact Ht
    imodintro; iexact HR
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- L1's junk below the frontier is absurd. -/
theorem junk1_front (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False) {π : Proto} {ws1 : PState}
    {v : Nat} (hvM : 1 ≤ v ∧ v ≤ M.length) (hv : v ≤ wfr ws1) (hJ : junk1 M v = true) :
    pCtxE (GF := GF) g M sv ∗ frontA g π img4 M ws1 ⊢ |={⊤}=> False := by
  iintro ⟨#Hctx, #Hfr⟩
  unfold pCtxE
  icases Hctx with ⟨Hdoom, -, -, Hjs⟩
  ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hjs
  imod frontS g M hdd (π := π) (img := img4) (ws := ws1) v ⟨hvM.1, hvM.2, hv⟩ $$ [] with #Hs
  · iframe Hdoom Hfr
  iapply junk_shot g v; iframe Hj Hs

/-! ## 5. The L1 acquire -/

/-- **THE L1 ACQUIRE**: the word is 1, or 0 with `Pub1E s` claimed from the release `s` it read. -/
theorem l1_acqE (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False) {π : Proto}
    {ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {ts : Nat} (hlen : tvs.length = 4)
    (hm : bytesAll (fun a t v => memByte img4 M t a = some v) L1 tvs)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) L1 tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (L1 + j) < ts)
    (hts : ts ≤ wfr ws1) :
    pCtxE (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ tk1 M sv ∗ £ 1 ⊢
      |={⊤}=> (tk1 M sv ∗ ⌜tvs.map Prod.snd = toBytes 1 4⌝) ∨
        (⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗ ∃ s, ⌜s < ts⌝ ∗ Pub1E g M sv s) := by
  iintro ⟨#Hctx, #Hfr, Htk, Hc⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hb : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img4 M t (L1 + j) = some v ∧ t < ts := fun j t v hj hg =>
    ⟨bytesAll_get hm hg, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj)⟩
  -- each source: the image, an L1 lock message, or junk (fulfilled: absurd)
  have step : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      pCtxE (GF := GF) g M sv ∗ frontA g π img4 M ws1 ⊢
        |={⊤}=> ⌜t = 0 ∨ knd M t = 2 ∨ knd M t = 3⌝ := fun j t v hj hg => by
    obtain ⟨hbt, hlt⟩ := hb j t v hj hg
    iintro ⟨#Hctx', #Hfr'⟩
    cases t with
    | zero => imodintro; ipureintro; exact .inl rfl
    | succ k =>
      obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hbt)
      have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm'
      rcases l1_cls hmt hj (by rw [hba]; rfl) with h | h | h
      · imodintro; ipureintro; exact .inr (.inl (of_decide_eq_true h))
      · imodintro; ipureintro; exact .inr (.inr (of_decide_eq_true h))
      · imod junk1_front g M sv hdd (π := π) (ws1 := ws1) (msgAt_le hmt) (by omega) h $$ [] with %hf
        · iframe Hctx' Hfr'
        exact hf.elim
  imod step 0 t0 v0 (by decide) rfl $$ [] with %hc0
  · iframe Hctx Hfr
  imod step 1 t1 v1 (by decide) rfl $$ [] with %hc1
  · iframe Hctx Hfr
  imod step 2 t2 v2 (by decide) rfl $$ [] with %hc2
  · iframe Hctx Hfr
  imod step 3 t3 v3 (by decide) rfl $$ [] with %hc3
  · iframe Hctx Hfr
  obtain ⟨hb0, hs0⟩ := hb 0 t0 v0 (by decide) rfl
  have hword : [v0, v1, v2, v3] = toBytes (if knd M t0 = 3 then 0 else 1) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp)
      (l1_val (by decide) hb0 hc0) (l1_val (by decide) (hb 1 t1 v1 (by decide) rfl).1 hc1)
      (l1_val (by decide) (hb 2 t2 v2 (by decide) rfl).1 hc2) (l1_val (by decide) (hb 3 t3 v3 (by decide) rfl).1 hc3)
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases h3 : knd M t0 = 3
  · rw [if_pos h3] at hword
    have ht0 : 1 ≤ t0 := by
      cases t0 with
      | zero => cases h3
      | succ k => omega
    have ht0M : t0 ≤ M.length := by
      cases hmt : msgAt M t0 with
      | none => unfold knd at h3; rw [hmt] at h3; cases h3
      | some m => exact (msgAt_le hmt).2
    unfold pCtxE
    icases Hctx with ⟨Hdoom, Hl1, -⟩
    imod frontS g M hdd (π := π) (img := img4) (ws := ws1) t0 ⟨ht0, ht0M, by omega⟩ $$ [] with #Hsh
    · iframe Hdoom Hfr
    unfold tk1
    icases bsl_filter_take (fun t => token (GF := GF) (sv.tk t)) (isK M 3) (fun _ => false) t0
      (by simp [isK, h3]) (fun _ h => by cases h) (rng M) (mem_rng.2 ⟨ht0, ht0M⟩) (nodup_rng M) $$ Htk
      with ⟨Ht, -⟩
    ihave #Hsl := bsl_mem (F := fun t => l1SlotE g M sv t)
      (List.mem_filter.2 ⟨mem_rng.2 ⟨ht0, ht0M⟩, by simp [isK, h3]⟩) $$ Hl1
    imod l1_claimE g M sv t0 $$ [Ht Hc] with HP
    · iframe Hsl Hsh Ht Hc
    imodintro; iright
    isplitr
    · ipureintro; rw [hmap, hword]
    · iexists t0; iframe HP; ipureintro; exact hs0
  · rw [if_neg h3] at hword
    imodintro; ileft; iframe Htk; ipureintro; rw [hmap, hword]

/-! ## 6. The L2 acquire, by ownership -/

/-- **ONE L2 BYTE** (R-a4 by ownership): read with a floor `fl ≥ lo`, `lo` writing the byte, below the frontier: its
source is `lo` — a later L2 message's `pend` is in hart 1's bag (absurd once fulfilled), one touching L1 is junk. -/
theorem l2_byteE (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False) {π : Proto} {ws1 : PState}
    {lo ex t j fl : Nat} {v : BitVec 8} (hj : j < 4) (hlw : wrB M (Lk + j) lo) (hfl : lo ≤ fl)
    (hm : memByte img4 M t (Lk + j) = some v) (hr : ¬ writesIn M (Lk + j) t fl) (ht : t ≤ wfr ws1)
    (hex : t ≠ ex) :
    pCtxE (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ zBagE g M sv lo ex ⊢
      |={⊤}=> zBagE g M sv lo ex ∗ ⌜t = lo⌝ := by
  iintro ⟨#Hctx, #Hfr, Hz⟩
  have hlt : lo ≤ t := by
    apply Classical.byContradiction; intro hlt
    obtain ⟨m, hm', hba⟩ := hlw
    obtain ⟨k, hk⟩ : ∃ k, lo = k + 1 := by
      cases lo with
      | zero => cases hm'
      | succ k => exact ⟨k, rfl⟩
    exact hr ⟨lo, by omega, hfl, m, by rw [hk] at hm' ⊢; simpa [msgAt] using hm', hba⟩
  by_cases heq : t = lo
  · imodintro; iframe Hz; ipureintro; exact heq
  cases t with
  | zero => omega
  | succ k =>
    obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hm)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm'
    have htM := msgAt_le hmt
    rcases l2_cls hmt hj (by rw [hba]; rfl) with h | h
    · unfold pCtxE
      icases Hctx with ⟨Hdoom, -⟩
      imod frontS g M hdd (π := π) (img := img4) (ws := ws1) (k + 1) ⟨htM.1, htM.2, ht⟩ $$ [] with #Hsh
      · iframe Hdoom Hfr
      unfold zBagE zB
      icases Hz with ⟨Hp, -⟩
      icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ex) && isL2O M t) (fun _ => false)
        (k + 1) (by simp [h, hex]; omega) (fun _ h => by cases h) (rng M) (mem_rng.2 htM) (nodup_rng M) $$ Hp
        with ⟨Hp, -⟩
      iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod junk1_front g M sv hdd (π := π) (ws1 := ws1) htM ht h $$ [] with %hf
      · iframe Hctx Hfr
      exact hf.elim

/-- **THE ATOMICITY OF L2, BY OWNERSHIP**: the AMO at `ts` after the birth `b` (hart 1 holding the L2 bag above
`b`, except `ts`) is the first L2 write after `b`. -/
theorem l2_nxtE (g : AGN) (M : List PMsg) (sv : SV) (hdd : g.dd = fun _ => False) {π : Proto} {ws1 : PState}
    {b ts : Nat} (hbt : b < ts) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) :
    pCtxE (GF := GF) g M sv ∗ frontA g π img4 M ws1 ∗ zBagE g M sv b ts ⊢
      |={⊤}=> zBagE g M sv b ts ∗ ⌜nxtL M b ts⌝ := by
  iintro ⟨#Hctx, #Hfr, Hz⟩
  by_cases hn : nxtL M b ts
  · imodintro; iframe Hz; ipureintro; exact hn
  have hex : ∃ v, b < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hbt, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, m, hmv, hbv⟩ := hex
  have hvM := msgAt_le hmv
  rcases l2_cls hmv (j := 0) (by decide) (by simpa using hbv) with h | h
  · unfold pCtxE
    icases Hctx with ⟨Hdoom, -⟩
    imod frontS g M hdd (π := π) (img := img4) (ws := ws1) v ⟨hvM.1, hvM.2, by omega⟩ $$ [] with #Hsh
    · iframe Hdoom Hfr
    unfold zBagE zB
    icases Hz with ⟨Hp, -⟩
    icases bsl_filter_take (pend g) (fun t => decide (b < t) && decide (t ≠ ts) && isL2O M t) (fun _ => false)
      v (by simp [h, hv1]; omega) (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ Hp
      with ⟨Hp, -⟩
    iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod junk1_front g M sv hdd (π := π) (ws1 := ws1) hvM (by omega) h $$ [] with %hf
    · iframe Hctx Hfr
    exact hf.elim

end res

end Weak.Prom.OA.EP
