/-
Weak/Prom: **E-a2 — THE RE-SPLIT AT INITLOCK and the contended lock's steps** (stage E-a2; G4-review2.md §6 A-3′;
plan rev 7 §3 "Lock birth and deferred deposits", "Acquire", "Atomicity", "Opening", R-a4).

* `resplit5` — THE CRUX: the L2 word's bag above the birth `b` (every later L2 message's `pend` and claim token, any
  shape, any author — hart 0's page) becomes the lock's persistent protocol `lkB5 b`: each release-shaped word's
  `pend` → its release slot, each junk message's → `lkJunk`, and each hart `h < 3`'s own acquire words' `pend`s and
  own lock words' tokens → `hSlot5 h b`.  Nothing about who will acquire is used: the partition is by the
  message's author, for every hart of the machine.
* `hclaim5` — hart `h` takes its part with its boot token `ak h b`; `fdeposit5` / `fclaim5` — the publication's
  slot (persistent content: any number of readers).
* `l2_byte5` (R-a4): a byte of an L2 read whose floor covers the birth came from the birth, an acquire or a
  release word above it — junk above `b` and the flag's junk are FULFILLED (frontier) yet hold their `pend`.
* `chain5` (atomicity, as (1c)): a lock-word write between the source and the AMO is the hart's own, above its
  floor, hence in its own bag (absurd once fulfilled) or junk.
* `claim5` — at the birth, `b`'s saved-proposition slot (bslot_claim); at a release, its slot.
* `acq5` — the acquire AMO: 1 (held) or 0 with the claimed resource.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnAE2Defs

namespace Weak.Prom.OA.E2

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y Z)
open Weak.Prom.OA.P (L1 SV bSlot bth bthAt isLockAt cAt5 dshotD bslot_claim bth_wr)
open Weak.Prom.OA.E
open Weak.Prom.OA.EP (tL1 tL2 isL2O isCO zB zBagE src_floor)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

section lock

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [SavedPropG GF] [InvGS GF]

/-! ## 1. The re-split at initlock -/

theorem byH_ne {M : List PMsg} {h h' t : Nat} (hne : h ≠ h') (h1 : byH M h t = true) : byH M h' t = false := by
  simp only [byH, decide_eq_true_eq] at h1; simp only [byH, h1, Option.some.injEq, decide_eq_false_iff_not]; omega

theorem A2_L2O {M : List PMsg} {t : Nat} (h : isA2 M t = true) : isL2O M t = true :=
  (Bool.and_eq_true_iff.1 h).1
theorem R2_L2O {M : List PMsg} {t : Nat} (h : isR2 M t = true) : isL2O M t = true :=
  (Bool.and_eq_true_iff.1 h).1

/-- **THE RE-SPLIT AT INITLOCK** (see the header). -/
theorem resplit5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (b : Nat) :
    zBagE (GF := GF) g M sv b 0 ⊢ |={⊤}=> lkB5 g M sv ak b := by
  unfold zBagE
  iintro ⟨Hp, Ht⟩
  have ez : zB M b 0 = (rng M).filter (fun t => decide (b < t) && decide (t ≠ 0) && isL2O M t) := rfl
  rw [ez]
  -- the `pend`s: each hart's acquire words, the release words, the junk
  have pA : ∀ h t, (decide (b < t) && decide (t ≠ 0) && isA2 M t && byH M h t) = true →
      (decide (b < t) && decide (t ≠ 0) && isL2O M t) = true := fun h t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ⊢; exact ⟨ht.1.1, A2_L2O ht.1.2⟩
  ihave ⟨HA0, Hp⟩ := bsl_peel (pend (GF := GF) g) _ _ (pA 0) (rng M) $$ Hp
  ihave ⟨HA1, Hp⟩ := bsl_peel (pend (GF := GF) g) _ _ (fun t ht => by
    have := pA 1 t ht; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; simp only [Bool.and_eq_true] at ht
    simp [this, byH_ne (by decide : 1 ≠ 0) ht.2]) (rng M) $$ Hp
  ihave ⟨HA2, Hp⟩ := bsl_peel (pend (GF := GF) g) _ _ (fun t ht => by
    have := pA 2 t ht; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; simp only [Bool.and_eq_true] at ht
    simp [this, byH_ne (by decide : 2 ≠ 0) ht.2, byH_ne (by decide : 2 ≠ 1) ht.2]) (rng M) $$ Hp
  ihave ⟨HR, Hp⟩ := bsl_peel (pend (GF := GF) g) (fun t => decide (b < t) && isR2 M t) _ (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    simp [ht.1, R2_L2O ht.2, R2_A2 ht.2, show t ≠ 0 by omega]) (rng M) $$ Hp
  ihave ⟨HJ, -⟩ := bsl_peel (pend (GF := GF) g) (fun t => decide (b < t) && isJ2 M t) _ (fun t ht => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    have hJ := ht.2; unfold isJ2 at hJ; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hJ
    simp [ht.1, hJ.1.1, hJ.1.2, hJ.2, show t ≠ 0 by omega]) (rng M) $$ Hp
  -- the tokens: each hart's lock words
  have pL : ∀ h t, (decide (b < t) && decide (t ≠ 0) && (isA2 M t || isR2 M t) && byH M h t) = true →
      (decide (b < t) && decide (t ≠ 0) && isL2O M t) = true := fun h t ht => by
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ht ⊢
    exact ⟨ht.1.1, ht.1.2.elim A2_L2O R2_L2O⟩
  ihave ⟨HL0, Ht⟩ := bsl_peel (fun t => token (GF := GF) (sv.tk t)) _ _ (pL 0) (rng M) $$ Ht
  ihave ⟨HL1, Ht⟩ := bsl_peel (fun t => token (GF := GF) (sv.tk t)) _ _ (fun t ht => by
    have := pL 1 t ht; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; simp only [Bool.and_eq_true] at ht
    simp [this, byH_ne (by decide : 1 ≠ 0) ht.2]) (rng M) $$ Ht
  ihave ⟨HL2, -⟩ := bsl_peel (fun t => token (GF := GF) (sv.tk t)) _ _ (fun t ht => by
    have := pL 2 t ht; simp only [Bool.and_eq_true, decide_eq_true_eq] at this; simp only [Bool.and_eq_true] at ht
    simp [this, byH_ne (by decide : 2 ≠ 0) ht.2, byH_ne (by decide : 2 ≠ 1) ht.2]) (rng M) $$ Ht
  -- the invariants
  imod bsl_fupd (G := fun r => rSlot5 (GF := GF) g M sv.tk r) (fun r => by
    iintro Hp; unfold rSlot5; iapply inv_alloc; inext; ileft; iexact Hp) _ $$ HR with #Hrs
  imod bsl_fupd (G := fun t => lkJunk (GF := GF) g t) (fun t => junk_alloc g t) _ $$ HJ with #Hjs
  imod inv_alloc (ndot (ndot hN5 0) b) ⊤ iprop(obg (GF := GF) g M sv.tk 0 b 0 ∨ token (ak 0 b)) $$ [HA0 HL0]
    with #H0
  · inext; ileft; unfold obg bgA bgL; iframe HA0 HL0
  imod inv_alloc (ndot (ndot hN5 1) b) ⊤ iprop(obg (GF := GF) g M sv.tk 1 b 0 ∨ token (ak 1 b)) $$ [HA1 HL1]
    with #H1
  · inext; ileft; unfold obg bgA bgL; iframe HA1 HL1
  imod inv_alloc (ndot (ndot hN5 2) b) ⊤ iprop(obg (GF := GF) g M sv.tk 2 b 0 ∨ token (ak 2 b)) $$ [HA2 HL2]
    with #H2
  · inext; ileft; unfold obg bgA bgL; iframe HA2 HL2
  imodintro
  unfold lkB5
  rw [show List.range 3 = [0, 1, 2] from rfl]
  iframe Hrs Hjs
  iapply (BigSepL.bigSepL_cons).2; isplitr
  · unfold hSlot5; iexact H0
  iapply (BigSepL.bigSepL_cons).2; isplitr
  · unfold hSlot5; iexact H1
  iapply (BigSepL.bigSepL_cons).2; isplitr
  · unfold hSlot5; iexact H2
  iapply (BigSepL.bigSepL_nil).2; itrivial

/-- **HART `h` TAKES ITS PART** of the lock born at `b`. -/
theorem hclaim5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) {h b : Nat} (hh : h < 3) :
    lkB5 (GF := GF) g M sv ak b ∗ token (ak h b) ⊢ |={⊤}=> obg g M sv.tk h b 0 := by
  iintro ⟨#Hlk, Ht⟩
  unfold lkB5
  icases Hlk with ⟨-, -, Hhs⟩
  ihave #Hs := bsl_mem (F := fun h => hSlot5 g M sv.tk ak h b) (List.mem_range.2 hh) $$ Hhs
  unfold hSlot5
  imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (Hob | Ht')
  · imod Hclose $$ [Ht] with -
    · iright; iexact Ht
    imodintro; iexact Hob
  · iexfalso; iapply token_exclusive; iframe Ht Ht'

theorem fdeposit5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (r : Nat) :
    fSlot5 (GF := GF) g M sv ak r ∗ Pub5 g M sv ak r ⊢ |={⊤}=> shot g r := by
  iintro ⟨#Hs, #HP⟩
  unfold fSlot5
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  icases Hb with (>Hp | ⟨>#Hsh, _⟩)
  · imod shoot $$ Hp with #Hsh
    imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HP
    imodintro; iexact Hsh
  · imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HP
    imodintro; iexact Hsh

theorem fclaim5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (t : Nat) :
    fSlot5 (GF := GF) g M sv ak t ∗ shot g t ∗ £ 1 ⊢ |={⊤}=> Pub5 g M sv ak t := by
  iintro ⟨#Hs, #Hsh, Hc⟩
  unfold fSlot5
  imod inv_acc (E := ⊤) CoPset.subseteq_top $$ Hs with ⟨Hb, Hclose⟩
  imod (lc_fupd_elim_later (E := ⊤ \ ↑(ndot fN5 t))
      (P := iprop(pend g t ∨ (shot g t ∗ Pub5 g M sv ak t)))) $$ Hc Hb with Hb
  icases Hb with (Hp | ⟨_, #HP⟩)
  · iexfalso; iapply pend_shot; iframe Hp Hsh
  · imod Hclose $$ [] with -
    · inext; iright; iframe Hsh HP
    imodintro; iexact HP

/-! ## 2. Reading the lock word -/

/-- Junk of the lock above `b`, or the flag's junk, below the frontier is absurd. -/
theorem jk_front (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {img : Image} {ws1 : PState} {b v : Nat} (hvM : 1 ≤ v ∧ v ≤ M.length) (hv : v ≤ wfr ws1)
    (hJ : (decide (b < v) && isJ2 M v) = true ∨ fJ M v = true) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img M ws1 ⊢ |={⊤}=> False := by
  iintro ⟨#Hctx, #Hlk, #Hfr⟩
  unfold ctx5 lkB5
  icases Hctx with ⟨Hdoom, -, Hfj, -⟩
  icases Hlk with ⟨-, Hjs, -⟩
  imod frontS g M hdd (π := π) (img := img) (ws := ws1) v ⟨hvM.1, hvM.2, hv⟩ $$ [] with #Hs
  · iframe Hdoom Hfr
  rcases hJ with hJ | hJ
  · ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hjs
    iapply junk_shot g v; iframe Hj Hs
  · ihave #Hj := bsl_mem (F := fun t => lkJunk g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hfj
    iapply junk_shot g v; iframe Hj Hs

/-- **ONE L2 BYTE** (R-a4): its floor covers the birth `b`, it is below the frontier: its source is the birth, or an
acquire or release word above it. -/
theorem l2_byte5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws1 : PState} {b t j fl : Nat} {v : BitVec 8} (hj : j < 4) (hb : bthAt M Lk b) (hfl : b ≤ fl)
    (hm : memByte img5 M t (Lk + j) = some v) (hr : ¬ writesIn M (Lk + j) t fl) (ht : t ≤ wfr ws1) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img5 M ws1 ⊢
      |={⊤}=> ⌜t = b ∨ (b < t ∧ (isA2 M t = true ∨ isR2 M t = true))⌝ := by
  iintro ⟨#Hctx, #Hlk, #Hfr⟩
  have hbt := src_floor (bth_wr hj hb) hfl hr
  by_cases heq : t = b
  · imodintro; ipureintro; exact .inl heq
  cases t with
  | zero => omega
  | succ k =>
    obtain ⟨m, hm', hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hm)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm'
    have htM := msgAt_le hmt
    have jk : ∀ (hJ : (decide (b < k + 1) && isJ2 M (k + 1)) = true ∨ fJ M (k + 1) = true),
        ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img5 M ws1 ⊢
          |={⊤}=> ⌜k + 1 = b ∨ (b < k + 1 ∧ (isA2 M (k + 1) = true ∨ isR2 M (k + 1) = true))⌝ := fun hJ => by
      iintro H
      imod jk_front g M sv ak hdd htM ht hJ $$ H with %hf
      exact hf.elim
    rcases l2_src hmt hj (by rw [hba]; rfl) with hO | hF
    · rcases l2_cls hO with hA | hR | hJ
      · imodintro; ipureintro; exact .inr ⟨by omega, .inl hA⟩
      · imodintro; ipureintro; exact .inr ⟨by omega, .inr hR⟩
      · iapply jk (.inl (by simp [hJ]; omega)); iframe Hctx Hlk Hfr
    · iapply jk (.inr hF); iframe Hctx Hlk Hfr

/-- **THE ATOMICITY STEP** (as (1c)'s `lk_chain`): see the header. -/
theorem chain5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws1 ws : PState} {b lo s0 ts vpre : Nat} (hbs : b ≤ s0) (hs0 : s0 < ts) (hts : ts ≤ wfr ws1)
    (hwts : wrB M Lk ts) (hlo : lo ≤ max vpre (coh ws Lk)) (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img5 M ws1 ∗ obg g M sv.tk h lo ts ⊢
      |={⊤}=> obg g M sv.tk h lo ts ∗ ⌜nxtL M s0 ts⌝ := by
  iintro ⟨#Hctx, #Hlk, #Hfr, Hbag⟩
  by_cases hn : nxtL M s0 ts
  · imodintro; iframe Hbag; ipureintro; exact hn
  have hex : ∃ v, s0 < v ∧ v < ts ∧ wrB M Lk v := by
    apply Classical.byContradiction; intro hne
    exact hn ⟨hs0, hwts, fun v h1 h2 h3 => hne ⟨v, h1, h2, h3⟩⟩
  obtain ⟨v, hv1, hv2, hwv⟩ := hex
  obtain ⟨m, hmv, hbv⟩ := hwv
  have hvM := msgAt_le hmv
  have htid : tidAt M v = some h := by
    apply Classical.byContradiction; intro hne
    exact chain_excl hv1 hv2 ⟨m, hmv, hbv⟩ hne hx
  have hvl : lo < v := by
    apply Classical.byContradiction; intro hle
    obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
    exact hr ⟨k + 1, hv1, by omega, m, by simpa [msgAt] using hmv, hbv⟩
  have hbyH : byH M h v = true := by simp [byH, htid]
  have jk : ∀ (hJ : (decide (b < v) && isJ2 M v) = true ∨ fJ M v = true),
      ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img5 M ws1 ∗ obg g M sv.tk h lo ts ⊢
        |={⊤}=> obg g M sv.tk h lo ts ∗ ⌜nxtL M s0 ts⌝ := fun hJ => by
    iintro ⟨H1, H2, H3, _⟩
    imod jk_front g M sv ak hdd (π := π) (img := img5) hvM (Nat.le_of_lt (Nat.lt_of_lt_of_le hv2 hts)) hJ
      $$ [H1 H2 H3] with %hf
    · iframe H1 H2 H3
    exact hf.elim
  rcases l2_src hmv (j := 0) (by decide) (by simpa using hbv) with hO | hF
  · rcases l2_cls hO with hA | hR | hJ
    · unfold ctx5
      icases Hctx with ⟨Hdoom, -⟩
      imod frontS g M hdd (π := π) (img := img5) (ws := ws1) v ⟨hvM.1, hvM.2, by omega⟩ $$ [] with #Hsh
      · iframe Hdoom Hfr
      unfold obg bgA
      icases Hbag with ⟨HbA, -⟩
      icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && isA2 M t && byH M h t)
        (fun _ => false) v (by simp [hvl, show v ≠ ts by omega, hA, hbyH])
        (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbA with ⟨Hp, -⟩
      iexfalso; iapply pend_shot; iframe Hp Hsh
    · unfold ctx5
      icases Hctx with ⟨Hdoom, -⟩
      imod frontS g M hdd (π := π) (img := img5) (ws := ws1) v ⟨hvM.1, hvM.2, by omega⟩ $$ [] with #Hsh
      · iframe Hdoom Hfr
      unfold obg bgL
      icases Hbag with ⟨-, HbL⟩
      icases bsl_filter_take (fun t => token (sv.tk t))
        (fun t => decide (lo < t) && decide (t ≠ ts) && (isA2 M t || isR2 M t) && byH M h t) (fun _ => false) v
        (by simp [hvl, show v ≠ ts by omega, hR, hbyH]) (fun _ h => by cases h) (rng M) (mem_rng.2 hvM)
        (nodup_rng M) $$ HbL with ⟨Ht, -⟩
      unfold lkB5
      icases Hlk with ⟨Hrs, -⟩
      ihave #Hslot := bsl_mem (F := fun r => rSlot5 g M sv.tk r)
        (List.mem_filter.2 ⟨mem_rng.2 hvM, by simp [hR]; omega⟩) $$ Hrs
      unfold rSlot5
      imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, -⟩
      icases Hb with (Hp | ⟨_, Ht', _⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · iexfalso; iapply token_exclusive; iframe Ht Ht'
    · iapply jk (.inl (by simp [hJ]; omega)); iframe Hctx Hlk Hfr Hbag
  · iapply jk (.inr hF); iframe Hctx Hlk Hfr Hbag

/-- **THE CLAIM**: the AMO `ts` with `nxtL M s0 ts` takes the resource of its source — the birth's (deferred,
saved-proposition) slot or a release's slot. -/
theorem claim5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws1 : PState} {γ : GName} {b c s0 ts : Nat} (hn : nxtL M s0 ts)
    (hs0 : s0 = b ∨ (b < s0 ∧ isR2 M s0 = true)) (hts : ts ≤ wfr ws1) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ isLockAt M sv γ Lk (Rb5 g M c) b ∗ frontA g π img5 M ws1 ∗
      token (sv.tk ts) ∗ £ 1 ⊢
      |={⊤}=> ∃ lw sp, ⌜(lw ≤ sp ∨ lw = c) ∧ sp ≤ s0⌝ ∗ cPts5 g M lw ∗ pPts5 g M sp := by
  iintro ⟨#Hctx, #Hlk, #Hl, #Hfr, Ht, Hc⟩
  rcases hs0 with rfl | ⟨hbs, hR⟩
  · unfold isLockAt
    icases Hl with ⟨-, #Hds, #HsQ, #Hslot⟩
    imod bslot_claim M sv s0 ts hn iprop(Rb5 g M c ∗ token γ) $$ [Ht Hc] with HR
    · iframe Hslot Hds HsQ Ht Hc
    icases HR with >⟨HR, -⟩
    unfold Rb5
    icases HR with ⟨HC, HP⟩
    imodintro; iexists c; iexists 0; iframe HC HP; ipureintro; exact ⟨.inr rfl, Nat.zero_le _⟩
  · have hsM : 1 ≤ s0 ∧ s0 ≤ M.length := by
      obtain ⟨m, hm, _⟩ := clsB_iff.1 (Bool.and_eq_true_iff.1 hR).2; exact msgAt_le hm
    unfold ctx5
    icases Hctx with ⟨Hdoom, -⟩
    imod frontS g M hdd (π := π) (img := img5) (ws := ws1) s0 ⟨hsM.1, hsM.2, by have := hn.1; omega⟩ $$ []
      with #Hsh
    · iframe Hdoom Hfr
    unfold lkB5
    icases Hlk with ⟨Hrs, -⟩
    ihave #Hslot := bsl_mem (F := fun r => rSlot5 g M sv.tk r)
      (List.mem_filter.2 ⟨mem_rng.2 hsM, by simp [hR]; omega⟩) $$ Hrs
    unfold rSlot5
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
    icases Hb with (Hp | ⟨_, Ha, (HR | Hn)⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod Hclose $$ [Ht Ha] with -
      · iright; iframe Hsh Ha; iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
      unfold Rs5
      icases HR with ⟨⟨%lw, %hlw, HC⟩, HP⟩
      imodintro; iexists lw; iexists s0; iframe HC HP; ipureintro; exact ⟨.inl hlw, Nat.le_refl _⟩
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Ht Ht'

/-- **THE ACQUIRE** of the lock born at `b`: value `1` (held), or `0` with the claimed resource. -/
theorem acq5 (g : AGN) (M : List PMsg) (sv : SV) (ak : Nat → Nat → GName) (h : Nat) (hdd : g.dd = fun _ => False)
    {π : Proto} {ws ws2 ws1 : PState} {tvs : List (Nat × BitVec 8)} {γ : GName} {b c ts lo vpre : Nat}
    (hb : bthAt M Lk b) (hlen : tvs.length = 4)
    (hlo1 : loadOk img5 M ws vpre Lk tvs) (hex : exclOk M h Lk (tvs.map Prod.fst) ts)
    (hsrc : bytesAll (fun x u _ => u ≤ coh ws2 x) Lk tvs) (hcohB : ∀ j : Nat, j < 4 → coh ws2 (Lk + j) < ts)
    (hbv : b ≤ vpre) (hlo : lo ≤ max vpre (coh ws Lk)) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts)
    (hnoinv : ∀ t a, ¬ cmoAt M isInvalK t a) :
    ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ isLockAt M sv γ Lk (Rb5 g M c) b ∗ frontA g π img5 M ws1 ∗
      obg g M sv.tk h lo ts ∗ token (sv.tk ts) ∗ £ 1 ⊢
      |={⊤}=> (obg g M sv.tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 1 4⌝) ∨
        (obg g M sv.tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗
          ∃ lw sp, ⌜(lw ≤ sp ∨ lw = c) ∧ sp < ts⌝ ∗ cPts5 g M lw ∗ pPts5 g M sp) := by
  iintro ⟨#Hctx, #Hlk, #Hl, #Hfr, Hbag, Htok, Hc⟩
  obtain ⟨t0, v0, t1, v1, t2, v2, t3, v3, rfl⟩ : ∃ t0 v0 t1 v1 t2 v2 t3 v3,
      tvs = [(t0, v0), (t1, v1), (t2, v2), (t3, v3)] := by
    match tvs, hlen with
    | [(a, b), (c, d), (e, f), (i, j)], _ => exact ⟨a, b, c, d, e, f, i, j, rfl⟩
  have hw := loadOk_weak hlo1
  have hbyte : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      memByte img5 M t (Lk + j) = some v ∧ t < ts ∧ ∃ fl, b ≤ fl ∧ ¬ writesIn M (Lk + j) t fl := fun j t v hj hg => by
    have h1 := bytesAll_get hw hg
    refine ⟨h1.1, Nat.lt_of_le_of_lt (bytesAll_get hsrc hg) (hcohB j hj), ?_⟩
    rcases h1.2 with ⟨fl, hfl, h⟩ | ⟨fl, hfl, ti, hc, _⟩
    · exact ⟨fl, by omega, h⟩
    · exact absurd hc (hnoinv _ _)
  have step : ∀ (j t : Nat) (v : BitVec 8), j < 4 → [(t0, v0), (t1, v1), (t2, v2), (t3, v3)][j]? = some (t, v) →
      ctx5 (GF := GF) g M sv ak ∗ lkB5 g M sv ak b ∗ frontA g π img5 M ws1 ⊢
        |={⊤}=> ⌜(t = b ∨ (b < t ∧ (isA2 M t = true ∨ isR2 M t = true))) ∧
          some v = (toBytes (if isA2 M t = true then 1 else 0) 4)[j]?⌝ := fun j t v hj hg => by
    obtain ⟨hm, hlt, fl, hfl, hr⟩ := hbyte j t v hj hg
    iintro H
    imod l2_byte5 g M sv ak hdd hj hb hfl hm hr (by omega) $$ H with %hc
    imodintro; ipureintro
    exact ⟨hc, l2_val hj hb hm (hc.imp_right (fun h => h.2))⟩
  imod step 0 t0 v0 (by decide) rfl $$ [] with %⟨hc0, hv0⟩
  · iframe Hctx Hlk Hfr
  imod step 1 t1 v1 (by decide) rfl $$ [] with %⟨-, hv1⟩
  · iframe Hctx Hlk Hfr
  imod step 2 t2 v2 (by decide) rfl $$ [] with %⟨-, hv2⟩
  · iframe Hctx Hlk Hfr
  imod step 3 t3 v3 (by decide) rfl $$ [] with %⟨-, hv3⟩
  · iframe Hctx Hlk Hfr
  have hword : [v0, v1, v2, v3] = toBytes (if isA2 M t0 = true then 1 else 0) 4 :=
    lk_word (by split <;> simp) (by split <;> simp) (by split <;> simp) (by split <;> simp) hv0 hv1 hv2 hv3
  have hmap : [(t0, v0), (t1, v1), (t2, v2), (t3, v3)].map Prod.snd = [v0, v1, v2, v3] := rfl
  by_cases hA0 : isA2 M t0 = true
  · rw [if_pos hA0] at hword
    imodintro; ileft; iframe Hbag; ipureintro; rw [hmap, hword]
  · rw [if_neg hA0] at hword
    have hc0' : t0 = b ∨ (b < t0 ∧ isR2 M t0 = true) := by
      rcases hc0 with h | ⟨h1, h | h⟩
      · exact .inl h
      · exact absurd h hA0
      · exact .inr ⟨h1, h⟩
    obtain ⟨_, hs0, _⟩ := hbyte 0 t0 v0 (by decide) rfl
    obtain ⟨_, hr0⟩ := loadOk_b0 hlo1
    have hr0 : ¬ writesIn M Lk t0 (max vpre (coh ws Lk)) := by
      rcases hr0 with h | ⟨ti, hci, _⟩
      · exact h
      · exact absurd hci (hnoinv _ _)
    imod chain5 g M sv ak h hdd (ws1 := ws1) (ws := ws) (π := π) (b := b) (lo := lo) (s0 := t0) (ts := ts)
      (vpre := vpre) (by rcases hc0' with h | h <;> omega) hs0 hts hwts hlo hr0 hex.1 $$ [Hbag]
      with ⟨Hbag, %hn⟩
    · iframe Hctx Hlk Hfr Hbag
    imod claim5 g M sv ak hdd (ws1 := ws1) (π := π) (γ := γ) (c := c) hn hc0' hts $$ [Htok Hc]
      with ⟨%lw, %sp, %hls, HC, HP⟩
    · iframe Hctx Hlk Hl Hfr Htok Hc
    imodintro; iright; iframe Hbag
    isplitr
    · ipureintro; rw [hmap, hword]
    · iexists lw; iexists sp; iframe HC HP; ipureintro; exact ⟨hls.1, by omega⟩

end lock

end Weak.Prom.OA.E2
