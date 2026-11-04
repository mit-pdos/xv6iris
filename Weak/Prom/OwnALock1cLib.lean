/-
Weak/Prom: **G4 target (1c) on track (a): the spinlock's per-step lemmas over (1c)'s classes** (stage S4a part 3;
plan rev 7 §3 "Acquire", "Atomicity", "Opening"; copies of OwnALockLib.lean §2 and OwnALockAcq.lean over the classes
of OwnALock1cDefs.lean, where a release may be a PLAIN store and the lock resource carries the cpu field's bag).

* `lk_src` — a lock-word byte read below the frontier came from the image, an acquire or a release message, or the
  run is in free mode;
* `lk_chain` — THE ATOMICITY STEP: an AMO at `ts` that read byte `Lk` from `s0` has `nxtL M s0 ts`;
* `lk_claim` — THE CLAIM: the acquirer at `ts` takes `Rs s0` out of the slot of `s0`;
* `lk_acq` — THE ACQUIRE: value `1` (held), or `0` with `Rs s0` for the read source `s0 < ts`, or free mode.
The proofs are (1a)'s verbatim: they never look inside `Rs`, and a release's class (`excl` or `plain`) does not
enter them.
No `sorry`, no axiom, no `native_decide`.
-/
import Weak.Prom.OwnALock1cDefs

namespace Weak.Prom.OA.C

open MachCSL MachCSL.Stdpp Iris.Std
open Weak (Image Dsrc)
open Weak.Prom Weak.Prom.PF Weak.Prom.Mach Weak.Prom.Mach.Cert
open Weak.Prom.Ref (Instr Test two64)
open Weak.Prom.Ref.Lit (X Y)
open PLabel
open Iris Iris.ProgramLogic Iris.BI Iris.ProofMode

/-! ## 2. The lock step lemmas -/

section steps

variable {GF : BundledGFunctors} [GhostVarG GF HSt] [GhostVarG GF Bool] [TokenG GF] [InvGS GF]

/-- Free mode from the context. -/
theorem lk_free_of (g : AGN) (M : List PMsg) (tk : Nat → GName) :
    lkCtx (GF := GF) g M tk ∗ dfree g ⊢ |={⊤}=> dfree g ∗ dshot g := by
  iintro ⟨#Hctx, #Hf⟩
  unfold lkCtx
  icases Hctx with ⟨Hdoom, -⟩
  imod dfree_dshot (E := ⊤) CoPset.subseteq_top g M $$ [] with #Hd
  · iframe Hdoom Hf
  imodintro
  iframe Hf Hd

/-- **A LOCK-WORD BYTE READ BELOW THE FRONTIER** came from the image, an acquire or a release message, or free mode. -/
theorem lk_src (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 : PState} {t j : Nat}
    {v : BitVec 8} (hj : j < 4) (hb : memByte img M t (Lk + j) = some v) (ht : t ≤ wfr ws1) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ ⌜t = 0 ∨ isA M t = true ∨ isR M t = true⌝ := by
  iintro ⟨#Hctx, #Hfr⟩
  cases t with
  | zero => imodintro; iright; ipureintro; exact .inl rfl
  | succ k =>
    obtain ⟨m, hm, hba⟩ := Option.bind_eq_some_iff.1 (by simpa [memByte] using hb)
    have hmt : msgAt M (k + 1) = some m := by simpa [msgAt] using hm
    have hw : wrB M (Lk + j) (k + 1) := ⟨m, hmt, by rw [hba]; rfl⟩
    rcases wrL_cls hj hw with hA | hR | hJ
    · imodintro; iright; ipureintro; exact .inr (.inl hA)
    · imodintro; iright; ipureintro; exact .inr (.inr hR)
    · unfold lkCtx
      icases Hctx with ⟨Hdoom, -, -, Hdd⟩
      ihave #Hd := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 (msgAt_le hmt), hJ⟩) $$ Hdd
      ihave #Hft := frontA_get (k + 1) $$ Hfr %⟨(msgAt_le hmt).1, (msgAt_le hmt).2, ht⟩
      imod dead_shot g M (k + 1) $$ [] with ⟨#Hf, #Hs⟩
      · iframe Hdoom Hd Hft
      imodintro; ileft; iframe Hf Hs

/-- **THE ATOMICITY STEP** (plan §3 "Atomicity"; see the header). -/
theorem lk_chain (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 ws : PState}
    {h lo s0 ts vpre : Nat} (hs0 : s0 < ts) (hts : ts ≤ wfr ws1) (hwts : wrB M Lk ts) (hlo : lo ≤ coh ws Lk)
    (hr : ¬ writesIn M Lk s0 (max vpre (coh ws Lk)))
    (hx : ¬ writesInBy M (fun tid => tid ≠ some h) Lk s0 (ts - 1)) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ obag g M tk h lo ts ⊢
      |={⊤}=> (obag g M tk h lo ts ∗ ⌜nxtL M s0 ts⌝) ∨ (dfree g ∗ dshot g) := by
  iintro ⟨#Hctx, #Hfr, Hbag⟩
  by_cases hn : nxtL M s0 ts
  · imodintro; ileft; iframe Hbag; ipureintro; exact hn
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
  ihave #Hft := frontA_get v $$ Hfr %⟨hvM.1, hvM.2, by omega⟩
  have hwv0 : wrB M (Lk + (0 : Nat)) v := by simpa using hwv
  rcases wrL_cls (by omega) hwv0 with hA | hR | hJ
  · -- an own acquire message above `lo`: its `pend` is in the bag
    unfold obag
    icases Hbag with ⟨HbA, -⟩
    unfold bagA
    icases bsl_filter_take (pend g) (fun t => decide (lo < t) && decide (t ≠ ts) && isA M t && byH M h t)
      (fun _ => false) v (by simp [hvl, show v ≠ ts by omega, hA, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbA with ⟨Hp, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · iexfalso; iapply pend_shot; iframe Hp Hsh
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- an own release message above `lo`: its token is in the bag, and its slot holds the author's token once shot
    unfold obag
    icases Hbag with ⟨-, HbL⟩
    unfold bagL
    icases bsl_filter_take (fun t => token (tk t))
      (fun t => decide (lo < t) && decide (t ≠ ts) && (isA M t || isR M t) && byH M h t) (fun _ => false) v
      (by simp [hvl, show v ≠ ts by omega, hR, hbyH])
      (fun _ h => by cases h) (rng M) (mem_rng.2 hvM) (nodup_rng M) $$ HbL with ⟨Ht, -⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · unfold lkCtx
      icases Hctx with ⟨-, -, Hrs, -⟩
      ihave #Hslot := bsl_mem (F := fun r => rSlot g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hvM, hR⟩) $$ Hrs
      unfold rSlot
      imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, -⟩
      icases Hb with (Hp | ⟨_, Ht', _⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · iexfalso; iapply token_exclusive; iframe Ht Ht'
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; iright; iframe Hf' Hd
  · -- junk or dead: free mode
    unfold lkCtx
    icases Hctx with ⟨Hdoom, -, -, Hdd⟩
    ihave #Hd := bsl_mem (F := fun t => deadInv g t) (List.mem_filter.2 ⟨mem_rng.2 hvM, hJ⟩) $$ Hdd
    imod dead_shot g M v $$ [] with ⟨#Hf, #Hs⟩
    · iframe Hdoom Hd Hft
    imodintro; iright; iframe Hf Hs

/-- **THE CLAIM** (plan §3 "Opening"): the acquirer at `ts` (holding the token of `ts`), whose read source `s0` is the
image or a release with `nxtL M s0 ts`, takes `Rs s0` (or the run is in free mode). -/
theorem lk_claim (g : AGN) (M : List PMsg) (tk : Nat → GName) {π : Proto} {img : Image} {ws1 : PState}
    {s0 ts : Nat} (hn : nxtL M s0 ts) (hs0 : s0 = 0 ∨ isR M s0 = true) (hts : ts ≤ wfr ws1) :
    lkCtx (GF := GF) g M tk ∗ frontA g π img M ws1 ∗ token (tk ts) ⊢
      |={⊤}=> (dfree g ∗ dshot g) ∨ Rs g M s0 := by
  iintro ⟨#Hctx, #Hfr, Ht⟩
  rcases hs0 with rfl | hR
  · unfold lkCtx
    icases Hctx with ⟨-, Hi, -⟩
    unfold iSlot
    imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hi with ⟨Hb, Hclose⟩
    icases Hb with (HR | Hn)
    · imod Hclose $$ [Ht] with -
      · iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
      imodintro; iright; iexact HR
    · unfold nxtTok
      icases Hn with ⟨%u, %hu, Ht'⟩
      rw [nxtL_unique hu hn] at *
      iexfalso; iapply token_exclusive; iframe Ht Ht'
  · have hsM : 1 ≤ s0 ∧ s0 ≤ M.length := by
      obtain ⟨m, hm, _⟩ := clsB_iff.1 hR; exact msgAt_le hm
    ihave #Hft := frontA_get s0 $$ Hfr %⟨hsM.1, hsM.2, by have := hn.1; omega⟩
    unfold fulT
    icases Hft with (#Hsh | ⟨#Hf, _⟩)
    · unfold lkCtx
      icases Hctx with ⟨-, -, Hrs, -⟩
      ihave #Hslot := bsl_mem (F := fun r => rSlot g M tk r) (List.mem_filter.2 ⟨mem_rng.2 hsM, hR⟩) $$ Hrs
      unfold rSlot
      imod inv_acc_timeless (E := ⊤) CoPset.subseteq_top $$ Hslot with ⟨Hb, Hclose⟩
      icases Hb with (Hp | ⟨_, Ha, (HR | Hn)⟩)
      · iexfalso; iapply pend_shot; iframe Hp Hsh
      · imod Hclose $$ [Ht Ha] with -
        · iright; iframe Hsh Ha; iright; unfold nxtTok; iexists ts; iframe Ht; ipureintro; exact hn
        imodintro; iright; iexact HR
      · unfold nxtTok
        icases Hn with ⟨%u, %hu, Ht'⟩
        rw [nxtL_unique hu hn] at *
        iexfalso; iapply token_exclusive; iframe Ht Ht'
    · imod lk_free_of g M tk $$ [] with ⟨#Hf', #Hd⟩
      · iframe Hctx Hf
      imodintro; ileft; iframe Hf' Hd

end steps


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
        (obag g M tk h lo ts ∗ ⌜tvs.map Prod.snd = toBytes 0 4⌝ ∗ ∃ s0, ⌜s0 < ts⌝ ∗ Rs g M s0) := by
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
      · imodintro; iright; iright; iframe Hbag
        isplitr
        · ipureintro; rw [hmap, hword]
        · iexists t0; iframe HR; ipureintro; omega
    · imodintro; ileft; iframe Hf Hd

end acq

end Weak.Prom.OA.C
